"""Untrusted scalar witnesses, kernel-checked violations and producer-free replay.

No search verdict, host calculation or saved theorem type is a proof. Reconstruct
the expected root from the frozen request, source and proposed witness values.
"""
import ast
from fractions import Fraction as Q
import json
import math
from pathlib import Path
import re
import shlex
import shutil
import time

from .emit import kernel_source, projection, real, returned
from .frontend import FRONTENDS, Unsupported, execute, number, parse, word


ENTRY = 'Workflow.Counterexample.counterexample'


def validate_request(request, program):
    selection = request['counterexample']
    if (not isinstance(selection, dict) or set(selection) != {'inputs', 'output'}
            or not isinstance(selection['inputs'], dict)
            or set(selection['inputs']) != set(program.inputs)
            or type(selection['output']) is not int
            or not 0 <= selection['output'] < len(program.outputs)):
        raise ValueError('counterexample needs exact input words and a zero-based output index')
    for value in selection['inputs'].values():
        if not isinstance(value, str) or not re.fullmatch(r'0x[0-9a-f]{16}', value):
            raise ValueError('Witness inputs must be lowercase 64-bit hexadecimal words: 0x + 16 digits')
        if not math.isfinite(number(int(value, 16))):
            raise ValueError('Witness inputs must be finite binary64 values')
    if (any((program.arrays, program.branches, program.counted, program.c,
             program.scientific, program.math, program.precision)) or request.get('python_method')
            or len(program.nodes) > 32 or (request.get('specification') is not None
                                          and not isinstance(request['specification'], list))):
        raise Unsupported('Counterexamples currently require a scalar rational reference and at most 32 separate binary64 graph nodes')
    if (request.get('target', 'lean') != 'lean' or request.get('proof') or request.get('rust_port')
            or request.get('producer', 'lean-flare') != 'lean-flare' or request.get('analysis_tools')):
        raise Unsupported('Counterexample witnesses use Lean delivery without a bound producer, authored proof or Rust port')


def exact_expression(source, inputs):
    """Candidate rational evaluation; Lean checks its equality to the reference."""
    def visit(node):
        if isinstance(node, ast.Name) and node.id in inputs:
            return inputs[node.id]
        if isinstance(node, ast.Constant) and type(node.value) in (int, float):
            return Q(ast.get_source_segment(source, node))
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -visit(node.operand)
        if isinstance(node, ast.BinOp):
            a, b = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Add): return a+b
            if isinstance(node.op, ast.Sub): return a-b
            if isinstance(node.op, ast.Mult): return a*b
            if isinstance(node.op, ast.Div):
                if b == 0: raise ValueError('Witness has a zero denominator in the independent reference')
                return a/b
        raise Unsupported('Counterexample reference requires rational scalar expressions')
    return visit(ast.parse(source, mode='eval').body)


def propose(program, request):
    bits = [int(request['counterexample']['inputs'][name], 16) for name in program.inputs]
    values = tuple(map(number, bits))
    actual = execute(program, values)
    if not all(math.isfinite(x) for x in actual):
        raise ValueError('This witness route requires finite outputs; exceptional outcomes need a separate property')
    inputs = dict(zip(program.inputs, map(Q.from_float, values), strict=True))
    return {'schema': 'numerics-witness-v1',
            'outputs': [f'0x{word(x):016x}' for x in actual],
            'reference': [str(exact_expression(x, inputs)) for x in request['specification']]}


def terms(program, request, record):
    if (not isinstance(record, dict) or record.get('schema') != 'numerics-witness-v1'
            or set(record) != {'schema', 'outputs', 'reference'}
            or not isinstance(record['outputs'], list) or not isinstance(record['reference'], list)
            or len(record['outputs']) != len(program.outputs) or len(record['reference']) != len(program.outputs)):
        raise ValueError('Malformed counterexample witness record')
    for bits in record['outputs']:
        if (not isinstance(bits, str) or not re.fullmatch(r'0x[0-9a-f]{16}', bits)
                or not math.isfinite(number(int(bits, 16)))):
            raise ValueError('Witness outputs must be finite binary64 hexadecimal words')
    if any(not isinstance(x, str) for x in record['reference']):
        raise ValueError('Witness reference values must be exact rational strings')
    witnesses = [f'(Float.ofBits {request["counterexample"]["inputs"][name]})' for name in program.inputs]
    args = ' '.join(witnesses)
    call = '(Workflow.kernel '+args+')'
    ref = '(Workflow.specification '+' '.join('(value '+x+')' for x in witnesses)+')'
    actuals = [f'(Float.ofBits {bits})' for bits in record['outputs']]
    selected = request['counterexample']['output']
    suffix = projection(selected, len(actuals))
    native = call+suffix
    reference = ref+suffix
    target = request['outputs'][selected]
    clauses = []
    for name, x in zip(program.inputs, witnesses, strict=True):
        lo, hi = request['domain'][name]
        clauses += [f'{x}.isFinite = true', f'{real(lo)} ≤ value {x}', f'value {x} ≤ {real(hi)}']
    clauses += [call+' = '+returned(actuals)]
    clauses += [call+projection(i, len(actuals))+'.isFinite = true' for i in range(len(actuals))]
    for i, bits in enumerate(record['outputs']):
        suffix_i = projection(i, len(actuals))
        clauses += ['value '+call+suffix_i+' = '+real(Q.from_float(number(int(bits, 16)))),
                    ref+suffix_i+' = '+real(Q(record['reference'][i]))]
    if target.get('property', 'absolute_error') == 'strict_positive':
        clauses += ['0 < '+reference, 'value '+native+' ≤ 0']
    else:
        clauses += [real(target['limit'])+' < |value '+native+' - '+reference+'|']
    return witnesses, actuals, call, ref, clauses


def value_lemma(name, bits):
    value = number(int(bits, 16))
    exponent = (int(bits, 16) >> 52) & 2047
    mantissa = int(bits, 16) & ((1 << 52)-1)
    if exponent: mantissa += 1 << 52
    if int(bits, 16) >> 63: mantissa = -mantissa
    proof = ['  rfl'] if value == 0 else [
        f'  change (({mantissa} : Int) : ℝ) * (2 : ℝ) ^ ({exponent-1075 if exponent else -1074} : Int) = _',
        '  norm_num']
    return [f'theorem {name} : value (Float.ofBits {bits}) = {real(Q.from_float(value))} := by', *proof, '']


def proof_source(program, request, record):
    witnesses, actuals, call, ref, clauses = terms(program, request, record)
    lines = ['module', 'public import Workflow.Kernel',
             'public import Mathlib.Tactic.NormNum', '', '@[expose] public section',
             'namespace Workflow.Counterexample', 'open Flare.Binary64.Value',
             'set_option maxRecDepth 10000', 'set_option maxHeartbeats 800000',
             # Exact binary64 subnormals require powers down to 2^-1074.
             'set_option exponentiation.threshold 1074', '']
    for i, name in enumerate(program.inputs):
        lines += value_lemma('input_value_'+str(i), request['counterexample']['inputs'][name])
    for i, bits in enumerate(record['outputs']):
        lines += value_lemma('output_value_'+str(i), bits)
    lines += [f'theorem execution : {call} = {returned(actuals)} := by', '  decide +kernel', '']
    names = [f'input_value_{i}' for i in range(len(witnesses))]
    lines += ['theorem counterexample :', '    '+' ∧\n    '.join(clauses)+' := by',
              '  refine ⟨'+', '.join(['?_']*len(clauses))+'⟩']
    # Closed native properties use the kernel evaluator. All interpreted real
    # identities and inequalities use exact rational normalization, never native_decide.
    for index in range(len(clauses)):
        if index < 3*len(witnesses) and index % 3 == 0:
            lines += ['  · decide +kernel']
        elif index < 3*len(witnesses):
            lines += [f'  · norm_num [input_value_{index//3}]']
        elif index == 3*len(witnesses):
            lines += ['  · exact execution']
        elif 3*len(witnesses) < index <= 3*len(witnesses)+len(actuals):
            lines += ['  · rw [execution]; decide +kernel']
        else:
            rewrite = ['Workflow.specification', 'execution', *names,
                       *[f'output_value_{i}' for i in range(len(actuals))]]
            lines += ['  · norm_num ['+', '.join(rewrite)+']']
    return '\n'.join([*lines, '', 'end Workflow.Counterexample', ''])


def check_source(program, request, record):
    clauses = terms(program, request, record)[-1]
    return '\n'.join(['module', 'import all Workflow.Proof',
        'meta import Lean.Util.CollectAxioms', 'open Flare.Binary64.Value', '',
        'example : '+' ∧\n    '.join(clauses)+' :=', '  '+ENTRY, '',
        'open Lean in', 'run_cmd do',
        '  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]',
        '  for axiomName in ← Lean.collectAxioms ``'+ENTRY+' do',
        '    unless allowed.contains axiomName do',
        '      throwError "Unexpected axiom {axiomName} in counterexample root"',
        '  logInfo "Requested counterexample type and transitive axioms checked independently."', ''])


def check_lean(output, request, program, record, runner, work):
    from .workflow import lean_environment
    environment, build = lean_environment(output, runner, work, request)
    (output/'lean/Workflow/Check.lean').write_text(check_source(program, request, record))
    for label, module in [('kernel', 'Kernel'), ('proof', 'Proof'), ('root-check', 'Check')]:
        target = build/'Workflow'/(module+'.olean'); target.parent.mkdir(parents=True, exist_ok=True)
        runner.run('lean-'+label, ['lean', '-DautoImplicit=false', '-DwarningAsError=true',
            '-Dlinter.extra=true', '-Dlinter.missingDocs=false', '-o', target, 'Workflow/'+module+'.lean'],
            cwd=output/'lean', env=environment)


def report(output, request, result):
    lines = ['# Numerical verification: '+result['status'], '', result['scope'], '',
             'Source: `'+result['source_path']+'`, function `'+request['function']+'`.', '',
             'Lean entry: `'+result.get('entry_theorem', 'not checked')+'`.', '', 'Witness inputs:']
    for name, bits in request['counterexample']['inputs'].items():
        lines += [f'- {name}: `{bits}` = {Q.from_float(number(int(bits,16)))}; domain {request["domain"][name]}.']
    for row in result.get('outputs', []):
        lines += ['', row['name']+' ('+row['unit']+'): '+row['evidence']+'.',
                  '- Binary64: '+row['bits']+' = '+row['value']+'.',
                  '- Independent exact reference: '+row['reference']+'.',
                  '- Attained absolute error: '+row['absolute_error']+'.']
    selected = request['outputs'][request['counterexample']['output']]
    requirement = ('strictly positive result and positive independent reference' if
                   selected.get('property') == 'strict_positive' else 'absolute error ≤ '+selected['limit'])
    lines += ['', 'Selected output: '+selected['name']+'.', 'Selected requirement: '+requirement+'.',
              'Violation is Lean-checked only when status is `counterexample`; no bound producer or search verdict proves it.',
              '', 'Trust boundaries:', *['- '+x for x in result['assumptions']]]
    if 'error' in result:
        lines += ['', 'Unresolved at `'+result['failure_stage']+'` ('+result['failure_kind']+'): '+result['error']]
    lines += ['', 'Reproduce or replay from a built FLARE checkout (choose new output directories):', '', '```sh',
              'python3 scripts/certify_numerics.py run --request '+shlex.quote(str(output/'request.json'))+' --out /absolute/path/to/new-run',
              'python3 scripts/certify_numerics.py replay --run '+shlex.quote(str(output))+' --out /absolute/path/to/new-replay', '```',
              'Replay checks frozen source models and the independent root without source execution or witness search.']
    (output/'report.md').write_text('\n'.join(lines)+'\n')


def certify(request_path, output):
    from .workflow import Runner, prepare, save, seal, sha
    from .runtimes import admit_runtime, source_results
    started = time.monotonic()
    request, source, program, questions = prepare(request_path)
    if questions: return {'status': 'needs_input', 'questions': questions}
    frozen = source.read_bytes()
    if parse(program.language, frozen.decode(), program.function, python_module=request.get('python_module'),cpp_module=request.get('cpp_module')) != program:
        raise ValueError('Source changed during admission; start a fresh run')
    output = Path(output).resolve(); output.mkdir(parents=True, exist_ok=False)
    source_name = 'source'+source.suffix
    request = {**request, 'source': source_name}
    save(output/'request.json', request); (output/source_name).write_bytes(frozen)
    save(output/'program.json', program.record())
    result = {'schema': 'numerics-run-v1', 'status': 'unresolved', 'kind': 'counterexample',
        'completed_stages': ['source_admitted'], 'source_path': str(source),
        'source_sha256': sha(output/source_name), 'source_language': program.language, 'target': 'lean',
        'source_assurance': FRONTENDS[program.language].assurance,
        'scope': 'One admissible binary64 witness refuting the selected requirement of the frozen scalar source model.',
        'assumptions': ['The admitted frontend maps source to the ordered scalar graph; its implementation is trusted.',
            'The selected runtime/compiler/hardware implements separate nearest/even binary64 operations with gradual underflow and no reassociation or implicit FMA.',
            'The independent exact reference, engineering domain and requirement need review. Physical/model uncertainty is excluded.']}
    if program.selection:
        result['source_selection']=program.selection
        result['assumptions'].append(program.selection['qualification'])
    runner = Runner(output, request.get('timeout_seconds',120)); work = output/'.work'; work.mkdir()
    try:
        runner.last_stage = 'source-runtime-admission'
        runtime = admit_runtime(program, request, output, work, runner)
        result['source_runtime'] = runtime['kind']
        result['completed_stages'].append('source_runtime_admitted')
        runner.last_stage = 'witness-proposal'
        record = propose(program, request); save(output/'witness.json', record)
        result['completed_stages'].append('witness_proposed')
        result['outputs'] = [{'name': t['name'], 'unit': t['unit'], 'bits': bits,
            'value': str(Q.from_float(number(int(bits,16)))), 'reference': exact,
            'absolute_error': str(abs(Q.from_float(number(int(bits,16)))-Q(exact))), 'evidence': 'proposed'}
            for t,bits,exact in zip(request['outputs'],record['outputs'],record['reference'],strict=True)]
        lean = output/'lean/Workflow'; lean.mkdir(parents=True)
        (lean/'Kernel.lean').write_text(kernel_source(program, request['specification']))
        (lean/'Proof.lean').write_text(proof_source(program, request, record))
        check_lean(output, request, program, record, runner, work)
        result['entry_theorem'] = ENTRY; result['completed_stages'].append('lean_root_checked')
        runner.last_stage = 'source-diagnostics'
        case = tuple(int(request['counterexample']['inputs'][name],16) for name in program.inputs)
        actual = source_results(program, frozen.decode(), [case], runtime, output, work, runner, request)
        if actual != [tuple(int(x,16) for x in record['outputs'])]:
            raise ValueError('Original source runtime and Lean-checked witness output disagree')
        save(output/'witness-diagnostics.json', {'inputs':request['counterexample']['inputs'],
            'outputs':record['outputs'], 'qualification':'Actual-source witness diagnostic only; source/runtime correspondence remains trusted.'})
        result['completed_stages'].append('source_diagnostics_checked')
        result['status'] = 'counterexample'
        result['violated_output'] = request['counterexample']['output']
        for row in result['outputs']: row['evidence'] = 'checked'
    except (RuntimeError, ValueError, OSError, ArithmeticError) as error:
        result.update(error=str(error), failure_stage=getattr(runner, 'last_stage', 'admission'))
        result['failure_kind'] = getattr(error, 'kind', 'stage_rejected')
        stage = output/'runs'/result['failure_stage']/'run.json'
        if stage.is_file():
            status = json.loads(stage.read_text())['status']
            if status == 'timeout': result['failure_kind'] = 'timeout'
            elif status == 'launch_error': result['failure_kind'] = 'missing_tool'
            elif 'maximum number of heartbeats' in (stage.parent/'stdout.txt').read_text():
                result['failure_kind'] = 'heartbeats'
    finally:
        result['elapsed_seconds'] = time.monotonic()-started
        report(output, request, result); shutil.rmtree(work); seal(output, result)
    return result


def replay(path, output, *, timeout_seconds=None):
    from .workflow import Runner, prepare, save
    request, source, program, questions = prepare(path/'request.json', replay=True)
    if questions: raise ValueError('Frozen counterexample request is incomplete')
    original = json.loads((path/'result.json').read_text())
    if original.get('status') != 'counterexample' or 'lean_root_checked' not in original.get('completed_stages', []):
        raise ValueError('This run has no completed counterexample root to replay')
    if kernel_source(program, request['specification']) != (path/'lean/Workflow/Kernel.lean').read_text():
        raise ValueError('Saved kernel/specification does not match the frozen original source/request')
    record = json.loads((path/'witness.json').read_text())
    terms(program, request, record)
    output = Path(output).resolve(); output.mkdir(parents=True, exist_ok=False)
    shutil.copytree(path/'lean', output/'lean')
    shutil.copyfile(path/'request.json', output/'request.json')
    shutil.copyfile(source, output/request['source'])
    shutil.copyfile(path/'witness.json', output/'witness.json')
    runner = Runner(output, timeout_seconds if timeout_seconds is not None else request.get('timeout_seconds',120)); work = output/'.work'; work.mkdir()
    try:
        check_lean(output, request, program, record, runner, work)
    finally:
        shutil.rmtree(work)
    result = {'status':'replayed', 'certificate_status':'counterexample', 'entry_theorem':ENTRY,
              'qualification':'Fresh Lean root-type and axiom check without witness search, producers or source runtime execution.'}
    save(output/'replay.json', result)
    return result
