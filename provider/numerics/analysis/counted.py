"""One checked invariant contract for every iteration of admitted source loops."""
from dataclasses import replace
from fractions import Fraction as Q

from numerics.analysis.bounds import Bound, analyze, scale_normalized
from numerics.analysis.composition import contract_module, function_module, identity, native_bounds
from numerics.emit.scalar import applied, expression, hypotheses, params, proposition, real, returned
from numerics.integrations.registry import Proposal
from numerics.emit.specification import lean_expression


def local_program(program):
    return replace(program,language='ir',function='step',counted=None)


def specification(spec, program):
    if (not isinstance(spec,dict) or set(spec)!={'kind','initial','state','step'} or spec['kind']!='iterate' or
            any(not isinstance(spec.get(k),list) or len(spec[k])!=2 for k in ['initial','state','step']) or
            any(not isinstance(n,str) or not n.isidentifier() for n in spec['state']) or
            any(not isinstance(e,str) for k in ['initial','step'] for e in spec[k]) or
            len(set(spec['state']))!=2 or set(spec['state'])&set(program.inputs)):
        raise ValueError('Counted source requires an independent two-state iterate specification')
    names={n:'a'+str(i) for i,n in enumerate(program.inputs)}
    bindings={**names,**{name:'state.'+str(i+1) for i,name in enumerate(spec['state'])}}
    initial=returned([lean_expression(e,program.inputs) for e in spec['initial']])
    step=returned([lean_expression(e,(),bindings) for e in spec['step']])
    return initial,step


def model_source(program, request):
    local=local_program(program); key=identity(local.record())
    function='Workflow.Functions.F'+key
    slots=program.counted['state_slots']; count=program.counted['iterations']
    args=applied(program)
    initial,step=specification(request['specification'],program)
    lines=['module','','public import Workflow.Functions.F'+key,'',
           '@[expose] public section','','namespace Workflow','']
    for name,typ,exact in [('native','Float',False),('ideal','ℝ',True)]:
        declarations=' '.join(f'(a{i} : {typ})' for i in range(len(program.inputs)))
        fixed_declarations=' '.join(f'(a{i} : {typ})' for i in range(len(program.inputs)) if i not in slots)
        fixed_args=' '.join('a'+str(i) for i in range(len(program.inputs)) if i not in slots)
        call=' '.join('state.'+str(slots.index(i)+1) if i in slots else 'a'+str(i)
                      for i in range(len(program.inputs)))
        prefix='noncomputable def' if exact else 'def'
        lines += [f'{prefix} {name}Step {fixed_declarations} (state : {typ} × {typ}) : {typ} × {typ} :=',
                  f'  {function}.'+('ideal' if exact else 'native')+' '+call,'',
                  f'{prefix} {name}Run (count : Nat) {declarations} : {typ} × {typ} :=',
                  f'  (List.replicate count ()).foldl (fun state _ => {name}Step {fixed_args} state) '+
                  returned(['a'+str(i) for i in slots]),'']
    for name,typ,body in [('kernel','Float',f'nativeRun {count} {args}'),
                         ('reference','ℝ',f'idealRun {count} {args}'),
                         ('specification','ℝ',f'(List.replicate {count} ()).foldl (fun (state : ℝ × ℝ) _ => {step}) {initial}')]:
        declarations=' '.join(f'(a{i} : {typ})' for i in range(len(program.inputs)))
        lines += [('def' if typ=='Float' else 'noncomputable def')+
                  f' {name} {declarations} : {typ} × {typ} :=', '  '+body,'']
    return '\n'.join([*lines,'end Workflow',''])


def proposed_inputs(program, request):
    """Closed, untrusted invariant search; its initialization/preservation are proved."""
    inputs={}
    slots=program.counted['state_slots']
    for i,name in enumerate(program.inputs):
        lo,hi=map(Q,request['domain'][name])
        if i in slots:
            if lo>0:
                lo,hi=lo/2,hi*2
            elif hi<0:
                lo,hi=lo*2,hi/2
            else:
                cap=max(abs(lo),abs(hi),Q(1))
                lo,hi=-2*cap,2*cap
            error=Q(request['outputs'][slots.index(i)]['limit'])
        else:
            error=Q(0)
        inputs['a'+str(i)]=Bound((lo+hi)/2,(hi-lo)/2,max(abs(lo),abs(hi)),error)
    return inputs


def proposal(program, request):
    local=local_program(program)
    inputs=proposed_inputs(program,request)
    bounds,steps=analyze(local,request['domain'],scale_normalized,input_bounds=inputs)
    fk=identity(local.record()); function='Workflow.Functions.F'+fk
    ck=identity({'function':fk,'bounds':{name:b.record() for name,b in bounds.items()},'steps':steps})
    contract='Workflow.Contracts.C'+ck
    modules={'Workflow/Functions/F'+fk+'.lean':function_module(local,fk),
             'Workflow/Contracts/C'+ck+'.lean':contract_module(local,bounds,steps,fk,ck)}
    args=applied(program); slots=program.counted['state_slots']; count=program.counted['iterations']
    claims={name:replace(bounds[name],e=inputs['a'+str(slot)].e)
            for slot,name in zip(slots,program.outputs,strict=True)}
    hyps=['    '+h for h in hypotheses(program,request['domain'])]
    def relation(n,i):
        return ' ∧ '.join(native_bounds(inputs['a'+str(slot)],f'{n}.{k+1}',f'{i}.{k+1}')
                          for k,slot in enumerate(slots))
    refargs=' '.join('(value a'+str(i)+')' for i in range(len(program.inputs)))
    fixedargs=' '.join('a'+str(i) for i in range(len(program.inputs)) if i not in slots)
    fixedrefs=' '.join('(value a'+str(i)+')' for i in range(len(program.inputs)) if i not in slots)
    lines=['module','','public import Workflow.Kernel','public import '+contract,
           'public import Flare.Analysis.ErrorRecurrence','', '@[expose] public section','',
           'namespace Workflow.Counted','open Flare.Binary64.Pipeline Flare.Binary64.Value','',
           'set_option maxHeartbeats 2000000','set_option maxRecDepth 4096','',
           'theorem invariant (count : Nat) '+params(program),*hyps,
           '    : '+relation(f'(nativeRun count {args})',f'(idealRun count {refargs})')+' := by',
           '  let R := fun (_ : Nat) (n : Float × Float) (i : ℝ × ℝ) => '+relation('n','i')]
    for i,_ in enumerate(program.inputs):
        b=inputs['a'+str(i)]
        lines += [f'  have b_a{i} : '+native_bounds(b,'a'+str(i),'(value a'+str(i)+')')+' := by',
                  '    refine ⟨h'+str(i)+'.1, ?_, ?_, ?_⟩',
                  '    · rw [abs_le]; constructor <;> linarith only [h'+str(i)+'.2.1, h'+str(i)+'.2.2]',
                  '    · rw [abs_le]; constructor <;> linarith only [h'+str(i)+'.2.1, h'+str(i)+'.2.2]',
                  '    · simp only [sub_self, abs_zero]; norm_num']
    lines += ['  have hstep : ∀ k < count, ∀ x : Unit, True → ∀ n i, R k n i →',
              f'      R (k+1) (nativeStep {fixedargs} n) (idealStep {fixedrefs} i) := by',
              '    intro _ _ _ _ n i h']
    nativeargs=' '.join('n.'+str(slots.index(k)+1) if k in slots else 'a'+str(k) for k in range(len(program.inputs)))
    idealargs=' '.join('i.'+str(slots.index(k)+1) if k in slots else '(value a'+str(k)+')' for k in range(len(program.inputs)))
    facts=' '.join('h.'+str(slots.index(k)+1) if k in slots else 'b_a'+str(k) for k in range(len(program.inputs)))
    lines += [f'    have hlocal := {contract}.bounds {nativeargs} {idealargs} {facts}',
              '    constructor']
    for index,name in enumerate(program.outputs):
        lines += [f'    · exact native_weaken hlocal.{index+1} (by norm_num) (by norm_num) (by norm_num)']
    initial=returned(['a'+str(i) for i in slots]); ideal_initial=returned(['(value a'+str(i)+')' for i in slots])
    lines += ['  have h := Flare.Analysis.ErrorRecurrence.foldl_contract',
              f'    (fun s (_ : Unit) => nativeStep {fixedargs} s)',
              f'    (fun s (_ : Unit) => idealStep {fixedrefs} s)',
              '    R (fun _ => True) count hstep (List.replicate count ()) (by simp)',
              f'    0 (by simp) {initial} {ideal_initial} ⟨'+', '.join('b_a'+str(i) for i in slots)+'⟩',
              '  simpa only [List.length_replicate, Nat.zero_add, nativeRun, idealRun] using h','',
              'theorem accuracy '+params(program),*hyps,'    : '+proposition(program,claims)+' := by',
              f'  have h := invariant {count} {args} '+' '.join('h'+str(i) for i in range(len(program.inputs))),
              '  exact ⟨h.1.finite, h.1.bounds.error, h.2.finite, h.2.bounds.error⟩','']
    initial_spec,step_spec=specification(request['specification'],program)
    sourceargs=['state.'+str(slots.index(k)+1) if k in slots else 'a'+str(k) for k in range(len(program.inputs))]
    import re
    substitute=lambda text:re.sub(r'\ba(\d+)\b',lambda m:'('+sourceargs[int(m[1])]+')',text)
    body='('+'; '.join('let '+node.name+' := '+substitute(expression(node,ideal=True)) for node in local.nodes)+\
         '; '+substitute(returned(local.outputs))+')'
    lines += ['theorem specification_equiv '+' '.join(f'(a{k} : ℝ)' for k in range(len(program.inputs))),
              f'    : reference {args} = specification {args} := by',
              f'  let sourceStep := fun (state : ℝ × ℝ) (_ : Unit) => idealStep {fixedargs} state',
              f'  let exactStep := fun (state : ℝ × ℝ) (_ : Unit) => {step_spec}',
              '  have hs : sourceStep = exactStep := by', '    funext state _input',
              '    change '+body+' = '+step_spec,'    apply Prod.ext <;> ring',
              f'  change (List.replicate {count} ()).foldl sourceStep '+returned(['a'+str(i) for i in slots])+\
              f' = (List.replicate {count} ()).foldl exactStep '+initial_spec,
              '  simp only [hs]','','end Workflow.Counted','']
    details={'validation':'lean-counted-invariant-v1','claim_policy':'checked-invariant-allowances',
        'iterations':count,'step_nodes':len(local.nodes),'expanded_operation_instances':count*sum(n.op!='constant' for n in local.nodes),
        'invariant':{name:b.record() for name,b in inputs.items()},'function_count':1,'contract_count':1,
        'qualification':'One preserved native/exact invariant for all natural horizons; the selected source count is instantiated at the root.'}
    return Proposal(bounds,[],claims,details,lean_source='\n'.join(lines),
        authored={'accuracy':'Workflow.Counted.accuracy','specification_equiv':'Workflow.Counted.specification_equiv'},
        modules=modules)
