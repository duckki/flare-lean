"""Guard-local scalar contracts; inactive arithmetic is not executed or assumed safe."""
import ast
from dataclasses import replace
from fractions import Fraction as Q

from numerics.analysis.bounds import Bound
from numerics.analysis.composition import function_module, identity
from numerics.emit.scalar import applied, expression, hypotheses, params, proposition, real, returned
from numerics.frontends.scalar import execute, number
from numerics.integrations.registry import Proposal
from numerics.analysis.scalar import constant_proof, proposal as scalar_proposal
from numerics.emit.specification import lean_expression, lean_specification


def arm_program(program, choice):
    output=program.nodes[-1].args[2 if choice else 3]
    nodes={n.name:n for n in program.nodes[:-1]}
    needed=set()
    def visit(name):
        if name in nodes and name not in needed:
            needed.add(name)
            for arg in nodes[name].args:visit(arg)
    visit(output)
    return replace(program,nodes=tuple(n for n in program.nodes if n.name in needed),
                   outputs=(output,),branches=None)


def execute_local(program, arguments):
    env={'a'+str(i):v for i,v in enumerate(arguments)}
    node=next(n for n in program.nodes if n.name==program.branches['constant'])
    env[node.name]=number(node.bits)
    branch=program.nodes[-1]; left,right=map(env.__getitem__,branch.args[:2])
    choice=left<right if branch.op=='select_lt' else left<=right
    return execute(arm_program(program,choice),arguments)


def arm_source(program, choice):
    arm=arm_program(program,choice)
    namespace='Workflow.BranchYes' if choice else 'Workflow.BranchNo'
    source=function_module(arm,identity(arm.record()))
    return source.replace('Workflow.Functions.F'+identity(arm.record()),namespace).replace(
        'def native ','def kernel ').replace('def ideal ','def reference ')


def guard(program, exact=False, decoded=False):
    branch=program.nodes[-1]; op='<' if branch.op=='select_lt' else '≤'
    node=next(n for n in program.nodes if n.name==program.branches['constant'])
    def name(ref):
        if ref==node.name:
            return real(Q.from_float(number(node.bits))) if exact else 'threshold'
        return '(value '+ref+')' if decoded else ref
    return name(branch.args[0])+' '+op+' '+name(branch.args[1])


def model_source(program, request, output):
    for choice in [True,False]:
        name='BranchYes' if choice else 'BranchNo'
        if (output/'lean/Workflow'/name/'Kernel.lean').read_text()!=arm_source(program,choice):
            raise ValueError('Saved local-branch model does not match frozen source')
    node=next(n for n in program.nodes if n.name==program.branches['constant'])
    args=applied(program)
    lines=['module','','public import Workflow.BranchYes.Kernel','public import Workflow.BranchNo.Kernel','',
           '@[expose] public section','','namespace Workflow','',
           'def threshold : Float := Float.ofBits '+str(node.bits),'']
    for name,typ,exact in [('kernel','Float',False),('reference','ℝ',True)]:
        declarations=' '.join(f'(a{i} : {typ})' for i in range(len(program.inputs)))
        lines += [('noncomputable def' if exact else 'def')+f' {name} {declarations} : {typ} :=',
                  '  if '+guard(program,exact)+' then BranchYes.'+name+' '+args+' else BranchNo.'+name+' '+args,'']
    declarations=' '.join(f'(a{i} : ℝ)' for i in range(len(program.inputs)))
    lines += [f'noncomputable def specification {declarations} : ℝ :=',
              *['  '+x for x in lean_specification(request['specification'],program)],'', 'end Workflow','']
    return '\n'.join(lines)


def domains(program, request):
    node=next(n for n in program.nodes if n.name==program.branches['constant'])
    cut=Q.from_float(number(node.bits)); variable=program.branches['variable']
    name=program.inputs[int(variable[1:])]; lo,hi=map(Q,request['domain'][name])
    variable_left=program.nodes[-1].args[0]==variable
    result=[]
    for choice in [True,False]:
        lower=(not variable_left) == choice
        a,b=(max(lo,cut),hi) if lower else (lo,min(hi,cut))
        result.append(None if a>b else {**request['domain'],name:[str(a),str(b)]})
    return result


def proposal(program, request):
    modules={}; proposals=[]; ds=domains(program,request)
    for choice,domain in zip([True,False],ds,strict=True):
        arm=arm_program(program,choice); name='BranchYes' if choice else 'BranchNo'
        modules['Workflow/'+name+'/Kernel.lean']=arm_source(program,choice)
        value=scalar_proposal(arm,{**request,'domain':domain}) if domain is not None else None
        proposals.append(value)
        if value is not None:
            modules['Workflow/'+name+'/Proof.lean']=value.lean_source.replace('public import Workflow.Kernel',
                'public import Workflow.'+name+'.Kernel').replace('Workflow.Scalar','Workflow.'+name+'.Scalar')
    feasible=[p.claims[next(iter(p.claims))] for p in proposals if p is not None]
    lo=min(b.c-b.w for b in feasible); hi=max(b.c+b.w for b in feasible)
    bound=Bound((lo+hi)/2,(hi-lo)/2,max(b.i for b in feasible),max(b.e for b in feasible))
    claims={program.outputs[0]:bound}
    args=applied(program); refargs=' '.join('(value a'+str(i)+')' for i in range(len(program.inputs)))
    node=next(n for n in program.nodes if n.name==program.branches['constant'])
    constant=constant_proof(replace(node,name='threshold'))
    constant[0]='  have p_threshold : value threshold = '+real(Q.from_float(number(node.bits)))+\
                ' := '+constant[0].split(' := ',1)[1]
    lines=['module','','public import Workflow.Kernel',
           *['public import Workflow.'+('BranchYes' if c else 'BranchNo')+'.Proof'
             for c,p in zip([True,False],proposals,strict=True) if p is not None],
           'public import Flare.Binary64.Order','','@[expose] public section','',
           'namespace Workflow.LocalBranches','open Flare.Binary64.Value','',
           'theorem accuracy '+params(program),*['    '+h for h in hypotheses(program,request['domain'])],
           '    : '+proposition(program,claims)+' := by',
           '  have hf : threshold.isFinite = true := by decide +kernel',
           *constant]
    variable=program.branches['variable']; finite='h'+variable[1:]+'.1'
    left,right=program.nodes[-1].args[:2]
    hleft=finite if left==variable else 'hf'; hright=finite if right==variable else 'hf'
    lines += ['  have horder : ('+guard(program)+') ↔ ('+guard(program,True,True)+') := by',
              '    rw [Flare.Binary64.Order.'+('lt_iff' if program.nodes[-1].op=='select_lt' else 'le_iff')+
              ' _ _ '+hleft+' '+hright+', p_threshold]',
              '  by_cases ht : '+guard(program,True,True)]
    for choice,domain,p in zip([True,False],ds,proposals,strict=True):
        name='BranchYes' if choice else 'BranchNo'
        if domain is None:
            facts=', '.join(['ht',*['h'+str(i)+'.2.'+str(k) for i in range(len(program.inputs)) for k in [1,2]]])
            lines += ['  · exfalso; linarith only ['+facts+']']
            continue
        lines += ['  · have hn : '+('' if choice else '¬ ')+ '('+guard(program)+') := '+
                  ('horder.mpr ht' if choice else 'fun h => ht (horder.mp h)'),
                  '    change (if '+guard(program)+' then BranchYes.kernel '+args+' else BranchNo.kernel '+args+').isFinite = true ∧',
                  '      |value (if '+guard(program)+' then BranchYes.kernel '+args+' else BranchNo.kernel '+args+') -',
                  '        (if '+guard(program,True,True)+' then BranchYes.reference '+refargs+' else BranchNo.reference '+refargs+')| ≤ '+real(bound.e),
                  '    rw [ite_eq_'+('left' if choice else 'right')+' hn, ite_eq_'+('left' if choice else 'right')+' ht]',
                  '    have h := Workflow.'+name+'.Scalar.accuracy '+args]
        for i,_ in enumerate(program.inputs):
            lines += ['      ⟨h'+str(i)+'.1, by linarith only [h'+str(i)+'.2.1, h'+str(i)+'.2.2, ht],',
                      '        by linarith only [h'+str(i)+'.2.1, h'+str(i)+'.2.2, ht]⟩']
        lines += ['    exact ⟨h.1, h.2.trans (by norm_num)⟩']
    spec=ast.parse(request['specification'][0],mode='eval').body
    if not isinstance(spec,ast.IfExp):
        raise ValueError('Guard-local source requires an independent exact conditional specification')
    lines += ['', 'theorem specification_equiv '+' '.join(f'(a{i} : ℝ)' for i in range(len(program.inputs))),
              '    : reference '+args+' = specification '+args+' := by',
              '  apply ite_congr', '  · apply propext', '    constructor <;> intro h <;> linarith']
    for choice,arm_expr in zip([True,False],[spec.body,spec.orelse],strict=True):
        arm=arm_program(program,choice)
        body='('+'; '.join('let '+n.name+' := '+expression(n,ideal=True) for n in arm.nodes)+\
             ('; ' if arm.nodes else '')+returned(arm.outputs)+')'
        lines += ['  · intro _','    change '+body+' = '+lean_expression(ast.unparse(arm_expr),program.inputs), '    ring']
    lines += ['','end Workflow.LocalBranches','']
    details={'validation':'lean-guard-local-v1','claim_policy':'checked-local-allowances',
        'domains':ds,'stable_flow_cases':2,'divergent_flow_cases':0,
        'qualification':'The direct finite-input guard agrees with its decoded-real guard; inactive-arm arithmetic is excluded, with branch premises proved locally.'}
    return Proposal(claims,[],claims,details,lean_source='\n'.join(lines),modules=modules,
        authored={'accuracy':'Workflow.LocalBranches.accuracy','specification_equiv':'Workflow.LocalBranches.specification_equiv'})
