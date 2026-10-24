"""Untrusted rational sqrt proposals; Lean checks endpoints and perturbation rules."""
from fractions import Fraction as Q
from math import isqrt

from numerics.analysis.bounds import Bound, up
from numerics.analysis import enclosure


def endpoints(value):
    """Propose dyadic root endpoints using integer arithmetic, never host sqrt."""
    from numerics.analysis.scalar import scale
    value=Q(value)
    if value < 0:
        raise ValueError('Square-root inference requires a nonnegative radicand')
    if not value:
        return Q(0),Q(0)
    grid=Q(2)**(scale(value)//2-96)
    scaled=value/(grid*grid)
    root=isqrt(scaled.numerator//scaled.denominator)
    lo=root*grid
    return lo,lo if lo*lo==value else (root+1)*grid


def analyze(parent, native, ideal, ranges, sqrt_input=False):
    from numerics.analysis.scalar import horner, interval, scale
    nlo,nhi=interval(horner(native),ranges) if native is not None else (parent.c-parent.w,parent.c+parent.w)
    ilo,ihi=interval(horner(ideal),ranges) if ideal is not None else (
        max(-parent.i,parent.c-parent.w-parent.e),min(parent.i,parent.c+parent.w+parent.e))
    if sqrt_input:
        nlo,ilo=max(Q(0),nlo),max(Q(0),ilo)
    if nlo < 0 or ilo < 0:
        raise ValueError('Cannot prove nonnegative native and exact square-root arguments; refine the domain or supply another proof route')
    lower,upper=endpoints(nlo)[0],endpoints(nhi)[1]
    ideal_upper=endpoints(ihi)[1]
    floor=min(lower,endpoints(ilo)[0])
    if floor:
        error=up(parent.e/(2*floor),scale(parent.e/(2*floor))-96)
        rule='positive-floor'
    else:
        error=endpoints(parent.e)[1]
        rule='squared-allowance'
    rho=up(Q(2)**-53*upper,scale(upper)-110)
    bound=Bound((lower+upper)/2,(upper-lower)/2+rho,ideal_upper,error+rho)
    return bound,{'native_range':(nlo,nhi),'ideal_range':(ilo,ihi),
        'lower':lower,'upper':upper,'ideal_upper':ideal_upper,'floor':floor,
        'incoming_allowance':error,'rounding_allowance':rho,'rule':rule,
        'source_native':native,'source_ideal':ideal,'sqrt_input':sqrt_input}


def evidence(proposal):
    return {key:([str(v) for v in value] if isinstance(value,tuple) else
                 value if isinstance(value,(str,bool)) else str(value))
            for key,value in proposal.items() if key not in ('source_native','source_ideal')}


def derive(step):
    """Emit a checked range/perturbation derivation for one actual native sqrt."""
    from numerics.analysis.scalar import real, horner, render
    node,b,data=step['node'],step['bound'],step['sqrt']
    name,parent=node.name,node.args[0]
    exact='(value '+parent+')' if parent.startswith('a') else 'i'+parent[1:]
    ni='i'+name[1:]
    lines=[]
    for label,poly,value in [('native',data['source_native'],'value '+parent),
                             ('ideal',data['source_ideal'],exact)]:
        lo,hi=data[label+'_range']
        lines += [f'  have {label}_{name} : {real(lo)} ≤ {value} ∧ {value} ≤ {real(hi)} := by']
        if poly is not None:
            if label=='native' and parent.startswith('n'):
                lines += [f'    rw [p_{parent}]']
            elif label=='ideal':
                lines += [f'    have polynomial : {exact} = {render(horner(poly))} := by ring!',
                          '    rw [polynomial]']
            lines += ['    '+line for line in enclosure.range_proof(horner(poly),lo,hi)]
        else:
            facts=[f'(abs_le.mp b_{parent}.bounds.centre).1',f'(abs_le.mp b_{parent}.bounds.centre).2']
            if label=='ideal':
                facts += [f'(abs_le.mp b_{parent}.bounds.error).1',f'(abs_le.mp b_{parent}.bounds.error).2',
                          f'(abs_le.mp b_{parent}.bounds.ideal).1',f'(abs_le.mp b_{parent}.bounds.ideal).2']
            if data['sqrt_input']:
                facts += [('nn_' if label=='native' else 'ni_')+parent]
            lines += ['    constructor <;> linarith only ['+', '.join(facts)+']']
    lo,hi=data['native_range'];ilo,ihi=data['ideal_range']
    lower,upper,j,d,floor,rho=[data[k] for k in ['lower','upper','ideal_upper','incoming_allowance','floor','rounding_allowance']]
    lines += [f'  have root_lo_{name} : {real(lower)} ^ 2 ≤ value {parent} := by',
              f'    have endpoint : {real(lower)} ^ 2 ≤ {real(lo)} := by norm_num',
              f'    exact endpoint.trans native_{name}.1',
              f'  have root_hi_{name} : value {parent} ≤ {real(upper)} ^ 2 := by',
              f'    have endpoint : {real(hi)} ≤ {real(upper)} ^ 2 := by norm_num',
              f'    exact native_{name}.2.trans endpoint',
              f'  have ideal_hi_{name} : {exact} ≤ {real(j)} ^ 2 := by',
              f'    have endpoint : {real(ihi)} ≤ {real(j)} ^ 2 := by norm_num',
              f'    exact ideal_{name}.2.trans endpoint',
              f'  have incoming_{name} : |Real.sqrt (value {parent}) - Real.sqrt {exact}| ≤ {real(d)} := by']
    if data['rule']=='positive-floor':
        lines += [f'    have native_floor : {real(floor)} ^ 2 ≤ value {parent} := by',
                  f'      exact (by norm_num : {real(floor)} ^ 2 ≤ {real(lo)}).trans native_{name}.1',
                  f'    have ideal_floor : {real(floor)} ^ 2 ≤ {exact} := by',
                  f'      exact (by norm_num : {real(floor)} ^ 2 ≤ {real(ilo)}).trans ideal_{name}.1',
                  f'    exact (Flare.Analysis.SqrtBounds.difference_le_of_floor _ _ _ _',
                  f'      (by norm_num : 0 < {real(floor)}) native_floor ideal_floor b_{parent}.bounds.error).trans (by norm_num)']
    else:
        lines += [f'    apply Flare.Analysis.SqrtBounds.difference_le_of_sq',
                  f'    · exact (by norm_num : (0 : ℝ) ≤ {real(lo)}).trans native_{name}.1',
                  f'    · exact (by norm_num : (0 : ℝ) ≤ {real(ilo)}).trans ideal_{name}.1',
                  '    · norm_num',f'    · exact b_{parent}.bounds.error.trans (by norm_num)']
    lines += [f'  have q_{name} := Flare.Binary64.SqrtPropagation.native_sqrt b_{parent}',
              f'    (l := {real(lower)}) (u := {real(upper)}) (j := {real(j)})',
              f'    (d := {real(d)}) (rho := {real(rho)})',
              '    (by norm_num) (by norm_num) (by norm_num)',
              f'    root_lo_{name} root_hi_{name} ideal_hi_{name} incoming_{name} (by norm_num)',
              f'  have b_{name} : NativeBounds {real(b.c)} {real(b.w)} {real(b.i)} {real(b.e)} {name} {ni} := by',
              f'    have checked := q_{name}.1', '    norm_num at checked ⊢', '    exact checked',
              f'  have nn_{name} : 0 ≤ value {name} := q_{name}.2',
              f'  have ni_{name} : 0 ≤ {ni} := Real.sqrt_nonneg _']
    return lines
