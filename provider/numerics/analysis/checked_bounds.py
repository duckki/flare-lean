"""Propose typed per-operation evidence; Lean independently checks every step.

This bounded product profile avoids expanding shared products into polynomials.
Exact-zero rules reuse FLARE's native semantics and keep incoming ideal errors.
"""
from fractions import Fraction as Q
from dataclasses import replace
from numerics.analysis.bounds import Bound, up
from numerics.analysis.scalar import U, TINY, scale, constant_proof
from numerics.emit.scalar import expression, hypotheses, params, proposition, real
from numerics.frontends.scalar import number
from numerics.integrations.registry import Proposal


CHECKER = 'Flare.Binary64.CheckedBounds'
MAX_OPERATIONS = 32
MAX_RATIONAL_BITS = 4096
MIN_SUMMARY_EXPONENT = -1200


def supported(program):
    return (not any([program.math, program.precision, program.arrays, program.branches,
                     program.counted, program.scientific, program.selection])
            and len(program.nodes) <= MAX_OPERATIONS
            and all(node.op in ('constant', 'mul') for node in program.nodes))


def summary(bound):
    def rat(value):
        return f'({value.numerator}/{value.denominator} : ℚ)'
    return '⟨'+', '.join(map(rat, [bound.c, bound.w, bound.i, bound.e]))+'⟩'


def bounded(values):
    if any(max(value.numerator.bit_length(), value.denominator.bit_length()) > MAX_RATIONAL_BITS
           for value in values):
        raise ValueError('Typed product evidence rational work limit exceeded')


def outward(value, precision):
    return up(value, max(scale(value)-precision, MIN_SUMMARY_EXPONENT))


def infer(program, domain):
    bounds, steps = {}, []
    for index, name in enumerate(program.inputs):
        endpoints = list(map(Q, domain[name])); bounded(endpoints)
        cap = max(map(abs, endpoints))
        bounds['a'+str(index)] = Bound(Q(0), cap, cap, Q(0))
    for node in program.nodes:
        rho, rule = Q(0), 'constant'
        if node.op == 'constant':
            value = Q.from_float(number(node.bits))
            bound = Bound(value, Q(0), abs(value), Q(0))
        else:
            a, b = [bounds[name] for name in node.args]
            cap = a.cap*b.cap
            if cap > Q(2)**1000:
                raise ValueError('Typed product evidence exceeds the finite nearest-rounding profile')
            rule = 'mul_zero' if not a.cap or not b.cap else 'mul'
            if rule == 'mul':
                rho = up(U*(cap+TINY), max(scale(cap)-110, MIN_SUMMARY_EXPONENT))
            # Recenter outward instead of squaring exact rational centers.
            # A fixed exponent floor also bounds tiny ideal magnitudes.
            radius = cap+rho
            ideal = a.i*b.i
            error = a.e*b.cap+a.i*b.e+rho
            bound = Bound(Q(0), outward(radius,80), outward(ideal,80), outward(error,96))
        bounded([bound.c,bound.w,bound.i,bound.e])
        bounds[node.name] = bound
        steps.append({'node':node.name, 'rule':rule, 'rounding_allowance':str(rho),
                      'summary':bound.record()})
    return bounds, steps


def proof_module(program, request, bounds, steps, claims):
    lines = ['module', '', 'public import Workflow.Kernel',
             'public import Flare.Binary64.CheckedBounds', '', '@[expose] public section',
             '', 'namespace Workflow.TypedBounds',
             'open Flare.Binary64.Pipeline Flare.Binary64.Value Flare.Binary64.CheckedBounds',
             '', 'set_option exponentiation.threshold 2048',
             'set_option maxRecDepth 4096', 'set_option maxHeartbeats 2000000', '',
             'theorem accuracy '+params(program),
             *['    '+h for h in hypotheses(program, request['domain'])],
             '    : '+proposition(program, claims)+' := by']
    for index, name in enumerate(program.inputs):
        key = 'a'+str(index); bound = bounds[key]
        lines += [f'  let s_{key} : Summary := {summary(bound)}',
                  f'  have b_{key} : s_{key}.Holds {key} (value {key}) := by',
                  f'    norm_num only [Summary.Holds, s_{key}, Rat.cast_div, Rat.cast_ofNat, div_one, zero_div]',
                  f'    apply same {key} 0 {real(bound.w)} {real(bound.i)} h{index}.1',
                  f'    all_goals rw [abs_le]; constructor <;> linarith only [h{index}.2.1, h{index}.2.2]']
    for node, step in zip(program.nodes, steps, strict=True):
        name = node.name; ideal = 'i'+name[1:]
        if node.op == 'constant':
            ideal_expr = real(Q.from_float(number(node.bits)))
        else:
            ideal_expr = ' * '.join('(value '+arg+')' if arg.startswith('a') else 'i'+arg[1:]
                                    for arg in node.args)
        lines += [f'  let {name} : Float := {expression(node)}',
                  f'  let {ideal} : ℝ := {ideal_expr}',
                  f'  let s_{name} : Summary := {summary(bounds[name])}']
        if node.op == 'constant':
            lines += constant_proof(node)
            lines += [f'  have b_{name} : s_{name}.Holds {name} {ideal} := by',
                      '    refine ⟨by decide +kernel, ?_, ?_, ?_⟩',
                      f'    all_goals norm_num [{ideal}, s_{name}, p_{name}]']
        else:
            a, b = node.args
            rho = Q(step['rounding_allowance'])
            args = f'(a := s_{a}) (b := s_{b}) (result := s_{name})'
            if step['rule'] == 'mul':
                args += f' (rho := ({rho.numerator}/{rho.denominator} : ℚ))'
            lines += [f'  have b_{name} : s_{name}.Holds {name} {ideal} := by',
                      f'    exact {step["rule"]}_sound {args} b_{a} b_{b} (by decide +kernel)']
    clauses=[]
    for name in program.outputs:
        clauses += [f'b_{name}.finite',f'b_{name}.bounds.error.trans (by norm_num)' ]
    lines += ['  exact ⟨'+', '.join(clauses)+'⟩', '', 'end Workflow.TypedBounds', '']
    return '\n'.join(lines)


def proposal(program, request, candidates=None, details=None):
    if not supported(program):
        raise ValueError('Typed product evidence requires at most 32 separately rounded product/constant nodes')
    bounds, steps = infer(program, request['domain'])
    limits = [Q(value) for value in candidates] if candidates is not None else [bounds[name].e for name in program.outputs]
    if len(limits) != len(program.outputs) or any(value < 0 for value in limits):
        raise ValueError('Expected one nonnegative typed candidate per output')
    bounded(limits)
    claims = {name:replace(bounds[name],e=limit) for name,limit in zip(program.outputs,limits,strict=True)}
    details = {**(details or {}), 'validation':'lean-typed-product-v1', 'rule_checker':CHECKER,
               'work_limits':{'max_ir_nodes':MAX_OPERATIONS,'max_rational_bits':MAX_RATIONAL_BITS,
                              'minimum_summary_exponent':MIN_SUMMARY_EXPONENT},
               'claim_policy':('producer-output-claims' if candidates is not None else 'checked-typed-inference'), 'foreign_trace_checked':False,
               'qualification':'Typed rational operation annotations are checked against native binary64 semantics, including incoming errors and exact-zero rules.'}
    return Proposal(bounds, steps, claims, details,
                    lean_source=proof_module(program,request,bounds,steps,claims),
                    authored={'accuracy':'Workflow.TypedBounds.accuracy'})
