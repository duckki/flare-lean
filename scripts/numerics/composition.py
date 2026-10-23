"""Compose source-helper contracts without expanding their ideal arguments.

Each module proves one local contract on arbitrary native and exact incoming
states, including their accumulated error. The application wires those checked
contracts to its original ordered graph. Module identities depend on contents,
so unchanged contracts can be reused when a caller or its horizon changes.
"""
import hashlib
import json
import re

from .analysis import analyze, scale_normalized
from .emit import applied, bound_derivation, expression, hypotheses, params, proposition, real, returned
from .specification import lean_expression, lean_specification
from .frontend import python_frontend
from .graph import Node, Program
from .integration import Proposal


def identity(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()[:24]


def groups(program, source, request):
    if program.language != 'python' or request.get('proof') or request.get('python_method'):
        return None
    trace = []
    parsed = python_frontend(source, request['function'], trace)
    if parsed != program:
        raise ValueError('Source helper trace does not match the admitted graph')
    selected = sorted((call for call in trace if call['depth'] == 1 and call['end'] > call['start']),
                      key=lambda call: call['start'])
    if len(selected) < 2 or selected[0]['start'] != 0 or selected[-1]['end'] != len(program.nodes):
        return None
    if any(a['end'] != b['start'] for a,b in zip(selected, selected[1:])):
        return None
    available = {'a'+str(i) for i in range(len(program.inputs))}
    for call in selected:
        nodes = program.nodes[call['start']:call['end']]
        internal = {node.name for node in nodes}
        external = {name for node in nodes for name in node.args if name not in internal}
        if not external <= available or any(name not in internal|available for name in call['outputs']):
            raise ValueError('Invalid helper graph boundary')
        available.update(call['outputs'])
    return selected if set(program.outputs) <= available else None


def local_program(program, call):
    nodes = program.nodes[call['start']:call['end']]
    internal = {node.name for node in nodes}
    inputs = list(dict.fromkeys(name for node in nodes for name in node.args if name not in internal))
    # A helper can return an unchanged argument without reading it in an operation.
    inputs += [name for name in call['outputs'] if name not in internal and name not in inputs]
    names = {name:'a'+str(i) for i,name in enumerate(inputs)}
    names.update({node.name:'n'+str(i) for i,node in enumerate(nodes)})
    local = Program('ir', 'helper', tuple('input'+str(i) for i in range(len(inputs))),
                    tuple(Node(names[node.name], node.op, tuple(names[x] for x in node.args), node.bits)
                          for node in nodes), tuple(names[name] for name in call['outputs']))
    return local, names, inputs


def native_bounds(bound, native, ideal):
    return 'NativeBounds '+' '.join(real(x) for x in [bound.c,bound.w,bound.i,bound.e])+' '+native+' '+ideal


def function_module(local, key):
    namespace = 'Workflow.Functions.F'+key
    lines = ['module', '', 'public import Flare.Binary64.Value', '', '@[expose] public section',
             '', 'namespace '+namespace, '']
    for name, typ, ideal in [('native','Float',False),('ideal','ℝ',True)]:
        prefix = 'noncomputable def' if ideal else 'def'
        out = typ if len(local.outputs) == 1 else typ+' × '+typ
        args = ' '.join(f'(a{i} : {typ})' for i in range(len(local.inputs)))
        lines += [f'{prefix} {name} {args} : {out} :=',
                  *[f'  let {node.name} := {expression(node, ideal=ideal)}' for node in local.nodes],
                  '  '+returned(local.outputs), '']
    return '\n'.join([*lines, 'end '+namespace, ''])


def contract_module(local, summaries, steps, function_key, key):
    namespace = 'Workflow.Contracts.C'+key
    function = 'Workflow.Functions.F'+function_key
    args = applied(local)
    exact_args = ' '.join('r'+str(i) for i in range(len(local.inputs)))
    lines = ['module', '', 'public import Workflow.Functions.F'+function_key,
             'public import Flare.Binary64.Pipeline', '', '@[expose] public section',
             '', 'namespace '+namespace, '', 'open Flare.Binary64.Pipeline Flare.Binary64.Value',
             '', 'set_option maxHeartbeats 2000000', 'set_option maxRecDepth 4096', '',
             'theorem bounds '+params(local),
             '    '+' '.join(f'(r{i} : ℝ)' for i in range(len(local.inputs)))]
    for i, _ in enumerate(local.inputs):
        lines += ['    (b_a'+str(i)+' : '+native_bounds(summaries['a'+str(i)], 'a'+str(i), 'r'+str(i))+')']
    clauses = []
    for index, name in enumerate(local.outputs):
        suffix = '.'+str(index+1) if len(local.outputs)>1 else ''
        clauses.append(native_bounds(summaries[name], f'({function}.native {args}){suffix}',
                                    f'({function}.ideal {exact_args}){suffix}'))
    lines += ['    : '+' ∧ '.join(clauses)+' := by']
    lines += bound_derivation(local, summaries, steps, {'a'+str(i):'r'+str(i) for i in range(len(local.inputs))})
    lines += ['  exact '+('⟨'+', '.join('b_'+name for name in local.outputs)+'⟩' if len(local.outputs)>1 else 'b_'+local.outputs[0])]
    return '\n'.join([*lines, '', 'end '+namespace, ''])


def model_source(program, specification, calls):
    """Preserve the admitted helper calls in native and exact executable models."""
    patterns = [local_program(program, call) for call in calls]
    keys = [identity(local.record()) for local, _, _ in patterns]
    lines = ['module', '', 'public import Flare.Binary64.Value',
             *['public import Workflow.Functions.F'+key for key in dict.fromkeys(keys)], '',
             '@[expose] public section', '', 'namespace Workflow', '']
    for name, typ, exact in [('kernel','Float',False),('reference','ℝ',True)]:
        values = {'a'+str(i):'a'+str(i) for i in range(len(program.inputs))}
        arguments = ' '.join(f'(a{i} : {typ})' for i in range(len(program.inputs)))
        out = typ if len(program.outputs)==1 else typ+' × '+typ
        lines += [('noncomputable def' if exact else 'def')+f' {name} {arguments} : {out} :=']
        for index, (call, pattern, key) in enumerate(zip(calls, patterns, keys, strict=True)):
            _, _, inputs = pattern
            args = ' '.join('('+values[arg]+')' for arg in inputs)
            lines += [f'  let state{index} := Workflow.Functions.F{key}.'+('ideal' if exact else 'native')+' '+args]
            for output, ref in enumerate(call['outputs']):
                values[ref] = 'state'+str(index)+('.'+str(output+1) if len(call['outputs'])>1 else '')
        lines += ['  '+returned([values[name] for name in program.outputs]), '']
    arguments = ' '.join(f'(a{i} : ℝ)' for i in range(len(program.inputs)))
    out = 'ℝ' if len(program.outputs)==1 else 'ℝ × ℝ'
    lines += [f'noncomputable def specification {arguments} : {out} :=',
              *['  '+line for line in lean_specification(specification,program)], '', 'end Workflow', '']
    return '\n'.join(lines)


def specification_proof(program, specification, calls):
    """Prove the helper/exact-step identity once, then rewrite the fold function."""
    if len(program.outputs) != 2 or program.outputs != calls[-1]['outputs']:
        return None
    patterns = [local_program(program, call) for call in calls]
    keys = [identity(local.record()) for local, _, _ in patterns]
    if len(set(keys)) != 1 or any(len(call['outputs']) != 2 for call in calls):
        return None
    inputs = [pattern[2] for pattern in patterns]
    try:
        state_slots = [inputs[1].index(name) for name in calls[0]['outputs']]
    except ValueError:
        return None
    if any(inputs[index][slot] != calls[index-1]['outputs'][component]
           for index in range(1,len(calls)) for component,slot in enumerate(state_slots)):
        return None
    fixed = {slot:names[0] for slot,names in enumerate(zip(*inputs)) if len(set(names)) == 1}
    observations = set(range(len(inputs[0])))-set(state_slots)-set(fixed)
    if len(observations) != 1:
        return None
    observation = observations.pop()
    if any(not refs[observation].startswith('a') for refs in inputs):
        return None
    source_args = [fixed[slot] if slot in fixed else 'state.'+str(state_slots.index(slot)+1)
                   if slot in state_slots else 'observation' for slot in range(len(inputs[0]))]
    source_step = 'Workflow.Functions.F'+keys[0]+'.ideal '+' '.join(source_args)
    local = patterns[0][0]
    def substitute(text):
        return re.sub(r'\ba(\d+)\b', lambda match:'('+source_args[int(match[1])]+')', text)
    source_value = '('+'; '.join('let '+node.name+' := '+substitute(expression(node, ideal=True))
                                for node in local.nodes)+'; '+substitute(returned(local.outputs))+')'
    names = {name:'a'+str(i) for i,name in enumerate(program.inputs)}
    bindings = {**names, specification['state'][0]:'state.1',specification['state'][1]:'state.2',
                specification['element']:'observation'}
    exact_step = '('+', '.join(lean_expression(expr, (), bindings) for expr in specification['step'])+')'
    source_sequence = '['+', '.join(refs[observation] for refs in inputs)+']'
    exact_sequence = '['+', '.join(names[name] for name in specification['sequence'])+']'
    source_initial = '('+', '.join(inputs[0][slot] for slot in state_slots)+')'
    exact_initial = '('+', '.join(lean_expression(expr, program.inputs) for expr in specification['initial'])+')'
    args = applied(program)
    return ['theorem specification_equiv '+' '.join(f'(a{i} : ℝ)' for i in range(len(program.inputs))),
            f'    : Workflow.reference {args} = Workflow.specification {args} := by',
            '  let sourceStep := fun (state : ℝ × ℝ) (observation : ℝ) => '+source_step,
            '  let exactStep := fun (state : ℝ × ℝ) (observation : ℝ) => '+exact_step,
            '  have hstep : sourceStep = exactStep := by', '    funext state observation',
            '    change '+source_value+' = '+exact_step,
            '    apply Prod.ext <;> ring',
            '  change '+source_sequence+'.foldl sourceStep '+source_initial+' = '+exact_sequence+'.foldl exactStep '+exact_initial,
            '  simp only [hstep]', '']


def proposal(program, request, calls):
    summaries, steps = analyze(program, request['domain'], scale_normalized)
    modules, contracts, functions, records = {}, [], {}, []
    native = {'a'+str(i):'a'+str(i) for i in range(len(program.inputs))}
    ideal = {name:'(value '+name+')' for name in native}
    body = []
    for index, call in enumerate(calls):
        local, names, inputs = local_program(program, call)
        local_bounds = {names[name]:summaries[name] for name in names}
        local_steps = [{**step, 'node': names[step['node']]} for step in steps[call['start']:call['end']]]
        function_key = identity(local.record())
        path = 'Workflow/Functions/F'+function_key+'.lean'
        function_source = function_module(local, function_key)
        if path in functions and functions[path] != function_source:
            raise ValueError('Helper module identity collision')
        if path not in functions:
            functions[path] = function_source
        key = identity({'function':function_key, 'bounds':{name:bound.record() for name,bound in local_bounds.items()},
                        'steps':local_steps})
        path = 'Workflow/Contracts/C'+key+'.lean'
        source = contract_module(local, local_bounds, local_steps, function_key, key)
        if path in modules and modules[path] != source:
            raise ValueError('Contract module identity collision')
        if path not in modules:
            modules[path] = source
        contracts.append(path)
        function = 'Workflow.Functions.F'+function_key
        n_args = ' '.join('('+native[name]+')' for name in inputs)
        r_args = ' '.join('('+ideal[name]+')' for name in inputs)
        facts = ' '.join('b_'+name for name in inputs)
        body += [f'  let state{index} := {function}.native {n_args}',
                 f'  let exact{index} := {function}.ideal {r_args}',
                 f'  have contract{index} := Workflow.Contracts.C{key}.bounds {n_args} {r_args} {facts}']
        for output, name in enumerate(call['outputs']):
            suffix = '.'+str(output+1) if len(call['outputs'])>1 else ''
            native[name], ideal[name] = f'state{index}'+suffix, f'exact{index}'+suffix
            body += [f'  have b_{name} : '+native_bounds(summaries[name], '('+native[name]+')', '('+ideal[name]+')')+
                     f' := contract{index}'+suffix]
        records.append({'helper':call['function'], 'start':call['start'], 'end':call['end'],
                        'inputs':inputs, 'outputs':call['outputs'], 'function_module':function,
                        'contract_module':'Workflow.Contracts.C'+key})
    modules = {**functions, **modules}
    lines = ['module', '', 'public import Workflow.Kernel',
             *['public import '+path[:-5].replace('/','.') for path in dict.fromkeys(contracts)],
             '', '@[expose] public section', '', 'namespace Workflow.Composed', '',
             'open Flare.Binary64.Pipeline Flare.Binary64.Value', '',
             'set_option maxHeartbeats 2000000', 'set_option maxRecDepth 4096', '',
             'theorem accuracy '+params(program),
             *['    '+h for h in hypotheses(program, request['domain'])],
             '    : '+proposition(program, summaries)+' := by']
    for i, _ in enumerate(program.inputs):
        b = summaries['a'+str(i)]
        lines += [f'  have b_a{i} : '+native_bounds(b, 'a'+str(i), '(value a'+str(i)+')')+' := by',
                  f'    apply same _ _ _ _ h{i}.1',
                  f'    all_goals rw [abs_le]; constructor <;> linarith only [h{i}.2.1, h{i}.2.2]']
    lines += body
    terms = []
    for name in program.outputs:
        terms += ['b_'+name+'.finite', 'b_'+name+'.bounds.error']
    lines += ['  exact ⟨'+', '.join(terms)+'⟩', '']
    authored = {'accuracy':'Workflow.Composed.accuracy'}
    specification = specification_proof(program, request['specification'], calls)
    if specification is not None:
        lines += specification
        authored['specification_equiv'] = 'Workflow.Composed.specification_equiv'
    lines += ['end Workflow.Composed', '']
    details = {'validation':'lean-helper-composition-v1', 'claim_policy':'checked-composed-allowances',
               'normalization':'scale-aware-outward-v1', 'helper_contracts':records,
               'function_count':len(functions), 'contract_count':len(set(contracts)),
               'qualification':'Every local contract accepts incoming native/exact state and accumulated error; the Lean root checks their original-graph composition.'}
    return Proposal(summaries, steps, {name:summaries[name] for name in program.outputs}, details,
                    lean_source='\n'.join(lines), authored=authored,
                    modules=modules, layout=calls)
