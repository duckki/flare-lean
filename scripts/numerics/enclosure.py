"""Emit typed enclosure evidence for the shared, proved Lean inference engine.

Python trees and endpoint calculations are untrusted. The Lean expression
interpreter checks every enclosure, including the original-variable premises.
Polynomial rewrites still need independent ring proofs in the calling module.
"""
from fractions import Fraction as Q


CHECKER = 'Flare.Analysis.IntervalExpression.Expr.check_sound'
RULES = ['rational', 'variable', 'add', 'mul', 'neg', 'pow']


def rational(value):
    value = Q(value)
    return f'({value.numerator} / {value.denominator} : ℚ)'


def expression(tree):
    op, *args = tree
    if op == 'constant':
        return '(.constant '+rational(args[0])+')'
    if op == 'variable':
        return '(.atom v_'+args[0]+')'
    if op == 'neg':
        return '(.neg '+expression(args[0])+')'
    if op in ('add', 'mul'):
        return '(.'+op+' '+expression(args[0])+' '+expression(args[1])+')'
    if op == 'pow' and type(args[1]) is int and 0 <= args[1] <= 16:
        return '(.pow '+expression(args[0])+' '+str(args[1])+')'
    raise ValueError('Unsupported shared enclosure rule: '+str(op))


def proof(tree, center, radius):
    """Prove a centered absolute bound through exact kernel computation."""
    term = expression(tree)
    if center:
        term = '(.add '+term+' (.constant '+rational(-center)+'))'
    # Atom definitions are local. Normalization unfolds their real interpretation,
    # never their proof or the endpoint computation used by the checker.
    names = sorted(variables(tree))
    definitions = ', '.join(['IntervalExpression.Expr.eval', *['v_'+name for name in names]])
    computation = ', '.join(['IntervalExpression.Expr.check', 'IntervalExpression.Expr.enclosure', *['v_'+name for name in names]])
    return [f'have checked := IntervalExpression.Expr.check_sound (e := {term})',
            f'  (lower := {rational(-radius)}) (upper := {rational(radius)}) (by dsimp only [{computation}]; decide +kernel)',
            f'norm_num only [{definitions}, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat] at checked',
            f'apply abs_le.mpr',
            f'constructor <;> linarith only [checked.1, checked.2]']


def variables(tree):
    op, *args = tree
    if op == 'variable':
        return {args[0]}
    if op == 'constant':
        return set()
    if op in ('pow', 'neg'):
        return variables(args[0])
    return variables(args[0]) | variables(args[1])


def atom(name, lo, hi, value):
    return [f'let v_{name} : IntervalExpression.Variable :=',
            f'  ⟨{rational(lo)}, {rational(hi)}, {value}, by',
            f'    constructor <;> norm_num <;> linarith only [{name}_lo, {name}_hi]⟩']


def range_proof(tree, lower, upper):
    """Check an asymmetric range without weakening it to a magnitude bound."""
    names=sorted(variables(tree))
    if not names:
        return ['norm_num']
    definitions=', '.join(['IntervalExpression.Expr.eval', *['v_'+name for name in names]])
    computation=', '.join(['IntervalExpression.Expr.check','IntervalExpression.Expr.enclosure', *['v_'+name for name in names]])
    return [f'have checked := IntervalExpression.Expr.check_sound (e := {expression(tree)})',
            f'  (lower := {rational(lower)}) (upper := {rational(upper)}) (by dsimp only [{computation}]; decide +kernel)',
            f'norm_num only [{definitions}, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat] at checked',
            'constructor <;> linarith only [checked.1, checked.2]']
