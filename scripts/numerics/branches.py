"""Reconstruct conditional error candidates with four Lean-checked flow cases.

The scalar procedure supplies native arithmetic laws. Branch guards are related
to real order only after finiteness is proved; both divergent flows remain in
scope. Foreign stable/unstable summaries never become theorem hypotheses.
"""
from dataclasses import replace
from fractions import Fraction as Q

from .analysis import Bound
from .emit import applied, proposition, real
from .integration import Proposal
from . import scalar


def proposal(program, request, candidates=None, details=None):
    branch = program.nodes[-1]
    if not program.branches or branch.op not in ('select_lt', 'select_le'):
        raise ValueError('Expected the admitted terminal conditional graph')
    arithmetic = replace(program, nodes=program.nodes[:-1], outputs=tuple(dict.fromkeys(branch.args)), branches=None)
    limit = Q(candidates[0]) if candidates is not None and len(candidates) == 1 else Q(request['outputs'][0]['limit'])
    if (candidates is not None and len(candidates) != 1) or limit < 0:
        raise ValueError('Expected one nonnegative conditional error candidate')
    root, leaves = scalar.plan(arithmetic, request['domain'], [limit]*len(arithmetic.outputs))
    summaries = dict(root['summaries'])
    arms = [summaries[name] for name in branch.args[2:]]
    lower, upper = min(b.c-b.w for b in arms), max(b.c+b.w for b in arms)
    summaries[branch.name] = Bound((lower+upper)/2, (upper-lower)/2, max(b.i for b in arms), limit)
    claims = {branch.name: summaries[branch.name]}

    def ideal(name):
        return '(value '+name+')' if name.startswith('a') else 'i'+name[1:]
    left, right, yes, no = branch.args
    operator = '<' if branch.op == 'select_lt' else '≤'
    native_test = left+' '+operator+' '+right
    exact_test = ideal(left)+' '+operator+' '+ideal(right)
    native = '(if '+native_test+' then '+yes+' else '+no+')'
    exact = '(if '+exact_test+' then '+ideal(yes)+' else '+ideal(no)+')'

    def finish(box):
        lines = ['  change '+native+'.isFinite = true ∧',
                 '    |value '+native+' - '+exact+'| ≤ '+real(limit),
                 '  by_cases hn : '+native_test+' <;> by_cases hi : '+exact_test]
        names = [*['a'+str(i) for i in range(len(program.inputs))], *[n.name for n in arithmetic.nodes]]
        definitions = ['i'+n.name[1:] for n in arithmetic.nodes]
        for native_choice, exact_choice in [(True, True), (True, False), (False, True), (False, False)]:
            selected = yes if native_choice else no
            lines += ['  · rw [ite_eq_'+('left' if native_choice else 'right')+' hn,',
                      '      ite_eq_'+('left' if exact_choice else 'right')+' hi]',
                      '    refine ⟨b_'+selected+'.finite, ?_⟩',
                      '    rw [Flare.Binary64.Order.'+('lt_iff' if branch.op == 'select_lt' else 'le_iff')+
                      ' _ _ b_'+left+'.finite b_'+right+'.finite] at hn']
            for name in names:
                lines += ['    have e_'+name+' := abs_le.mp b_'+name+'.bounds.error']
            if definitions:
                lines += ['    dsimp only ['+', '.join(definitions)+'] at hi '+
                          ' '.join('e_'+name for name in names)+' ⊢']
            facts = [item for name in names for item in ['e_'+name+'.1', 'e_'+name+'.2']]
            lines += ['    apply abs_le.mpr', '    constructor <;> linarith only ['+', '.join([*facts,'hn','hi'])+']']
        return lines

    source = scalar.proof_module(arithmetic, root, leaves, summaries,
        goal=proposition(program, claims), finish=finish)
    source += '\nnamespace Workflow.Branches\n\ntheorem specification_equiv '+\
        ' '.join('(a'+str(i)+' : ℝ)' for i in range(len(program.inputs)))+'\n'+\
        '    : reference '+applied(program)+' = specification '+applied(program)+' := by\n'+\
        '  apply ite_congr\n  · apply propext\n    constructor <;> intro h <;> linarith\n  · intro _; ring\n  · intro _; ring\n\nend Workflow.Branches\n'
    metadata = {**(details or {}), 'validation': 'lean-conditional-four-flows-v1',
        'claim_policy': 'producer-output-claims' if candidates is not None else 'requested-budget',
        'stable_flow_cases': 2, 'divergent_flow_cases': 2, 'boxes': len(leaves),
        'foreign_trace_checked': False,
        'qualification': 'All native/exact branch combinations and numerical premises are independently checked in Lean; no stable-test assumption.'}
    return Proposal(summaries, [], claims, metadata, lean_source=source,
        authored={'accuracy': 'Workflow.Scalar.accuracy', 'specification_equiv': 'Workflow.Branches.specification_equiv'})
