"""Reusable, untrusted scalar inference with independently checked Lean arguments.

Sparse polynomial normalization preserves correlations. Exact rational interval
search proposes rounding allowances and input splits; a proved Lean enclosure
engine and ring normalization check them against FLARE's native Float laws.
Higher-degree product graphs can fall back to typed native operation evidence.
No foreign bound, rewrite or Python calculation is a theorem premise.
"""
from dataclasses import replace
from fractions import Fraction as Q
import re

from numerics.analysis.bounds import Bound, up
from numerics.emit.scalar import applied, expression, hypotheses, params, proposition, real as rational_real
from numerics.frontends.scalar import number
from numerics.integrations.registry import Proposal
from numerics.analysis import enclosure


MAX_OPERATIONS = 32
MAX_TERMS = 256
MAX_DEGREE = 16
MAX_BOXES = 16
U, TINY = Q(2)**-53, Q(2)**-1022


def real(value):
    """Exact dyadic literals understood by Mathlib's existing interval family."""
    value = Q(value)
    if value.denominator == 1 or value.denominator & (value.denominator-1):
        return rational_real(value)
    power = value.denominator.bit_length()-1
    digits = str(abs(value.numerator)*5**power).rjust(power+1, '0')
    return '('+('-' if value < 0 else '')+digits[:-power]+'.'+digits[-power:]+' : ℝ)'


def supported(program):
    return len(program.nodes) <= MAX_OPERATIONS


def constant(value):
    return {(): Q(value)} if value else {}


def variable(name):
    return {((name, 1),): Q(1)}


def add(left, right, sign=1):
    result = dict(left)
    for powers, coefficient in right.items():
        result[powers] = result.get(powers, Q(0)) + sign*coefficient
        if not result[powers]:
            del result[powers]
    if len(result) > MAX_TERMS:
        raise ValueError('Scalar polynomial work limit exceeded')
    return result


def multiply(left, right):
    result = {}
    for a, x in left.items():
        for b, y in right.items():
            powers = dict(a)
            for name, count in b:
                powers[name] = powers.get(name, 0)+count
            if sum(powers.values()) > MAX_DEGREE:
                raise ValueError('Scalar polynomial work limit exceeded')
            key = tuple(sorted(powers.items()))
            result[key] = result.get(key, Q(0))+x*y
    result = {key: value for key, value in result.items() if value}
    if len(result) > MAX_TERMS:
        raise ValueError('Scalar polynomial work limit exceeded')
    return result


def horner(poly):
    """Factor a sparse polynomial; the independent Lean ring proof checks it.

    Retain powers across missing degrees instead of expanding x*x into two
    unrelated interval factors. This is essential for positive square floors.
    """
    names = sorted({name for powers in poly for name, _ in powers})
    if not names:
        return ('constant', poly.get((), Q(0)))
    name = names[0]
    groups = {}
    for powers, coefficient in poly.items():
        exponents = dict(powers)
        power = exponents.pop(name, 0)
        groups.setdefault(power, {})[tuple(sorted(exponents.items()))] = coefficient
    degrees = sorted(groups, reverse=True)
    result, previous = horner(groups[degrees[0]]), degrees[0]
    def times_power(value, power):
        if not power:
            return value
        factor = ('variable', name) if power == 1 else ('pow', ('variable', name), power)
        return factor if value == ('constant', Q(1)) else ('mul', factor, value)
    for degree in degrees[1:]:
        result = ('add', times_power(result, previous-degree), horner(groups[degree]))
        previous = degree
    return times_power(result, previous)


def interval(expr, ranges):
    op, *args = expr
    if op == 'constant':
        return args[0], args[0]
    if op == 'variable':
        return ranges[args[0]]
    if op == 'pow':
        lo, hi = interval(args[0], ranges)
        n = args[1]
        if not n:
            return Q(1), Q(1)
        if n % 2 or lo >= 0:
            return lo**n, hi**n
        return (hi**n if hi <= 0 else Q(0)), max(lo**n, hi**n)
    a, b = [interval(child, ranges) for child in args]
    if op == 'add':
        return a[0]+b[0], a[1]+b[1]
    products = [x*y for x in a for y in b]
    return min(products), max(products)


def render(expr):
    op, *args = expr
    if op == 'constant':
        return real(args[0])
    if op == 'variable':
        return '(value '+args[0]+')' if args[0].startswith('a') else args[0]
    if op == 'pow':
        return '('+render(args[0])+' ^ '+str(args[1])+')'
    return '('+render(args[0])+(' + ' if op == 'add' else ' * ')+render(args[1])+')'


def scale(value):
    value = abs(value)
    return value.numerator.bit_length()-value.denominator.bit_length() if value else -1022


def outward(lo, hi):
    # Relative precision retains tiny positive floors. One extra cell separates
    # proof-tactic enclosure rounding from the proposed endpoints.
    grid = Q(2)**(scale(max(abs(lo), abs(hi)))-96)
    return (lo//grid-1)*grid, up(hi, scale(grid))+grid


def input_range(lo, hi):
    return (lo, hi) if all(not (x.denominator & (x.denominator-1)) for x in [lo,hi]) else outward(lo,hi)


def magnitude(poly, ranges):
    lo, hi = interval(horner(poly), ranges)
    return max(abs(lo), abs(hi))


def analyze_box(program, domain):
    summaries, native, ideal, ranges, steps = {}, {}, {}, {}, []
    for index, name in enumerate(program.inputs):
        lo, hi = map(Q, domain[name])
        key = 'a'+str(index)
        summaries[key] = Bound((lo+hi)/2, (hi-lo)/2, max(abs(lo), abs(hi)), Q(0))
        native[key] = ideal[key] = variable(key)
        ranges[key] = input_range(lo, hi)
    operations={node.name:node.op for node in program.nodes}
    for node in program.nodes:
        extra={}
        pre = None
        zero = False
        if node.op == 'constant':
            value = Q.from_float(number(node.bits))
            native[node.name] = ideal[node.name] = constant(value)
            bound, rho, cap = Bound(value, Q(0), abs(value), Q(0)), Q(0), abs(value)
        elif node.op == 'round32':
            parent=node.args[0];a=summaries[parent]
            exponent=max(-126,scale(a.cap))
            if a.cap>Q(2)**exponent:exponent+=1
            if exponent>126:raise ValueError('Cannot prove finite binary32 storage within the selected magnitude range')
            cap=Q(2)**exponent;rho=Q(2)**(exponent-23)
            bound=Bound(a.c,a.w+rho,a.i,a.e+rho)
            native[node.name]=None;ideal[node.name]=ideal[parent]
            extra={'storage_exponent':exponent}
        elif node.op == 'sqrt':
            from numerics.analysis.square_root import analyze
            parent=node.args[0]
            bound,root=analyze(summaries[parent],native[parent],ideal[parent],ranges,operations.get(parent)=='sqrt')
            native[node.name]=ideal[node.name]=None
            rho,cap=root['rounding_allowance'],root['upper']
            extra={'sqrt':root}
        elif node.op == 'neg':
            a = summaries[node.args[0]]
            bound, rho, cap = Bound(-a.c, a.w, a.i, a.e), Q(0), a.cap
            for polys in [native, ideal]:
                parent = polys[node.args[0]]
                polys[node.name] = multiply(constant(-1), parent) if parent is not None else None
        else:
            left, right, *tail = node.args
            a, b = summaries[left], summaries[right]
            if node.op == 'div':
                lower, exact_lower = b.c-b.w, b.c-b.w-b.e
                if lower <= 0 or exact_lower <= 0:
                    raise ValueError(node.name+': cannot prove a positive native and exact denominator')
                cap = a.cap/lower
                raw = Bound(a.c/b.c, a.w/lower+abs(a.c)*b.w/(lower*b.c),
                            a.i/exact_lower, a.e/lower+a.i*b.e/(lower*exact_lower))
                native[node.name] = ideal[node.name] = None
            else:
                operation = multiply if node.op == 'mul' else lambda x, y: add(x, y, -1 if node.op == 'sub' else 1)
                for polys in [native, ideal]:
                    x, y = polys[left], polys[right]
                    if node.op == 'fma':
                        z = polys[tail[0]]
                        polys[node.name] = add(multiply(x, y), z) if all(p is not None for p in [x,y,z]) else None
                    else:
                        polys[node.name] = operation(x, y) if x is not None and y is not None else None
                pre = native[node.name]
                if node.op == 'fma':
                    c = summaries[tail[0]]
                    raw = Bound(a.c*b.c+c.c, a.w*b.cap+abs(a.c)*b.w+c.w,
                                a.i*b.i+c.i, a.e*b.cap+a.i*b.e+c.e)
                    cap = magnitude(pre, ranges) if pre is not None else a.cap*b.cap+c.cap
                elif node.op == 'mul':
                    cap = magnitude(pre, ranges) if pre is not None else a.cap*b.cap
                    raw = Bound(a.c*b.c, a.w*b.cap+abs(a.c)*b.w, a.i*b.i, a.e*b.cap+a.i*b.e)
                else:
                    cap = magnitude(pre, ranges) if pre is not None else a.cap+b.cap
                    raw = Bound(a.c+(-b.c if node.op == 'sub' else b.c), a.w+b.w, a.i+b.i, a.e+b.e)
                zero = node.op == 'add' and b.c == b.w == 0
            if cap > Q(2)**1000:
                raise ValueError('Scalar nearest-rounding magnitude exceeds the admitted profile')
            rho = Q(0) if zero else up(U*(cap+TINY), scale(cap)-110)
            if pre is not None:
                key = 'd'+node.name[1:]
                ranges[key] = -rho, rho
                native[node.name] = add(pre, variable(key))
                lo, hi = outward(*interval(horner(native[node.name]), ranges))
                error = magnitude(add(native[node.name], ideal[node.name], -1), ranges)
                bound = Bound((lo+hi)/2, (hi-lo)/2,
                              up(magnitude(ideal[node.name], ranges), scale(raw.i)-96),
                              up(error, scale(error)-96))
            else:
                lo, hi = outward(raw.c-raw.w-rho, raw.c+raw.w+rho)
                bound = Bound((lo+hi)/2, (hi-lo)/2, up(raw.i, scale(raw.i)-96),
                              up(raw.e+rho, scale(raw.e+rho)-96))
        summaries[node.name] = bound
        steps.append({'node': node, 'bound': bound, 'rho': rho, 'magnitude': cap,
                      'pre': pre, 'native': native[node.name], 'ideal': ideal[node.name], 'zero': zero,**extra})
    return summaries, steps


def plan(program, domain, limits):
    """Greedy, bounded split search. Leaf coverage is proved in the emitted Lean."""
    def leaf(box):
        summaries, steps = analyze_box(program, box)
        return {'domain': box, 'summaries': summaries, 'steps': steps}
    root = leaf(domain)
    leaves = [root]
    weights = [max(limit, Q(2)**-1075) for limit in limits]
    while len(leaves) < MAX_BOXES:
        failures = [box for box in leaves if any(box['summaries'][name].e > limit
                    for name, limit in zip(program.outputs, limits, strict=True))]
        if not failures:
            break
        box = max(failures, key=lambda b: max(b['summaries'][n].e/t for n,t in zip(program.outputs,weights,strict=True)))
        choices = []
        for name, endpoints in box['domain'].items():
            lo, hi = map(Q, endpoints)
            if lo == hi:
                continue
            mid = (lo+hi)/2
            children = [leaf({**box['domain'], name: [str(a), str(b)]}) for a,b in [(lo,mid),(mid,hi)]]
            score = max(child['summaries'][n].e/t for child in children for n,t in zip(program.outputs,weights,strict=True))
            choices.append((score, name, mid, children))
        current = max(box['summaries'][n].e/t for n,t in zip(program.outputs,weights,strict=True))
        if not choices or min(choice[0] for choice in choices) >= current:
            break
        _, name, mid, children = min(choices, key=lambda choice: (choice[0], choice[1]))
        box['split'] = (program.inputs.index(name), mid, children)
        leaves.remove(box); leaves.extend(children)
    return root, leaves


def constant_proof(node):
    bits = node.bits
    exponent, mantissa = (bits >> 52) & 2047, bits & ((1 << 52)-1)
    if exponent:
        mantissa += 1 << 52
    if bits >> 63:
        mantissa = -mantissa
    power = exponent-1075 if exponent else -1074
    value = Q.from_float(number(bits))
    return [f'  have p_{node.name} : value {node.name} = {real(value)} := by',
            f'    dsimp only [{node.name}]',
            f'    change ({mantissa} : ℝ) * (2 : ℝ) ^ ({power} : Int) = _', '    norm_num'] if value else [
                f'  have p_{node.name} : value {node.name} = (0 : ℝ) := by dsimp only [{node.name}]; rfl']


def proof_module(program, root, leaves, claims, *, goal=None, finish=None):
    args = applied(program)
    lines = ['module', '', 'public import Workflow.Kernel', 'public import Flare.Binary64.Pipeline',
             'public import Flare.Binary64.Nearest', 'public import Flare.Binary64.Zero',
             'public import Flare.Analysis.IntervalExpression', '',
             '@[expose] public section', '', 'namespace Workflow.Scalar',
             'open Flare.Binary64.Pipeline Flare.Binary64.Value',
             'open Flare.Analysis', '',
             'set_option maxHeartbeats 2000000', 'set_option maxRecDepth 4096', '']
    if program.precision:
        lines.insert(6,'public import Flare.Binary32.StorageBounds')
    if program.math and 'sqrt' in program.math['operations']:
        lines.insert(6,'public import Flare.Binary64.SqrtPropagation')
    lines += ['set_option exponentiation.threshold 2048', '']
    for index, box in enumerate(leaves):
        summaries = box['summaries']
        lines += [f'theorem box_{index} {params(program)}',
                  *['    '+h for h in hypotheses(program, box['domain'])],
                  '    : '+(goal or proposition(program, claims))+' := by']
        for i, _ in enumerate(program.inputs):
            b = summaries['a'+str(i)]
            lo, hi = input_range(*map(Q, box['domain'][program.inputs[i]]))
            lines += [f'  have a{i}_lo : {real(lo)} ≤ value a{i} := by linarith only [h{i}.2.1]',
                      f'  have a{i}_hi : value a{i} ≤ {real(hi)} := by linarith only [h{i}.2.2]',
                      f'  have b_a{i} : NativeBounds {real(b.c)} {real(b.w)} {real(b.i)} 0 a{i} (value a{i}) := by',
                      f'    apply same _ _ _ _ h{i}.1',
                      f'    all_goals rw [abs_le]; constructor <;> linarith only [h{i}.2.1, h{i}.2.2]']
            lines += ['  '+line for line in enclosure.atom('a'+str(i), lo, hi, 'value a'+str(i))]
        for step in box['steps']:
            node, b, rho, cap = (step[key] for key in ['node','bound','rho','magnitude'])
            name, ideal_name = node.name, 'i'+node.name[1:]
            parent_native = ['p_'+name for name in dict.fromkeys(node.args) if name.startswith('n')]
            ideal_expr = expression(node, ideal=True)
            ideal_expr = re.sub(r'\b[an]\d+\b', lambda m: '(value '+m[0]+')' if m[0].startswith('a') else 'i'+m[0][1:], ideal_expr)
            lines += [f'  let {name} : Float := {expression(node)}', f'  let {ideal_name} : ℝ := {ideal_expr}']
            target = f'NativeBounds {real(b.c)} {real(b.w)} {real(b.i)} {real(b.e)} {name} {ideal_name}'
            if node.op == 'constant':
                lines += constant_proof(node)
                lines += [f'  have b_{name} : {target} := by', '    refine ⟨by decide +kernel, ?_, ?_, ?_⟩',
                          f'    all_goals norm_num [{ideal_name}, p_{name}]']
            elif node.op == 'round32':
                parent=node.args[0];e=step['storage_exponent']
                lines += [f'  have b_{name} : {target} := by',
                    f'    have checked := Flare.Binary32.StorageBounds.native_roundTrip b_{parent} ({e})',
                    f'      (rho := {real(rho)}) (by norm_num) (by norm_num) (by norm_num) (by norm_num)',
                    '    norm_num at checked ⊢', '    exact checked']
            elif node.op == 'sqrt':
                from numerics.analysis.square_root import derive
                lines += derive(step)
            elif node.op == 'neg':
                proof = f'by simpa only [neg_neg, neg_zero, neg_div] using (native_neg b_{node.args[0]})'
                lines += [f'  have b_{name} : {target} := {proof}']
                if step['native'] is not None:
                    identity = (f'((congrArg Neg.neg {parent_native[0]}).trans (by ring))'
                                if parent_native else '(by ring)')
                    lines += [f'  have p_{name} : value {name} = {render(horner(step["native"]))} := by',
                              f'    exact (Flare.Binary64.Order.neg_value _ b_{node.args[0]}.finite).2.trans {identity}']
            else:
                left, right, *tail = node.args
                pre = expression(node, ideal=True)
                pre = re.sub(r'\b[an]\d+\b', lambda match: '(value '+match[0]+')', pre)
                lines += [f'  have m_{name} : |{pre}| ≤ {real(cap)} := by']
                if step['pre'] is not None:
                    expanded = render(horner(step['pre']))
                    parent_polys = {s['node'].name: s['native'] for s in box['steps']}
                    expanded_pre = re.sub(r'\(value (n\d+)\)',
                        lambda m: render(horner(parent_polys[m[1]])), pre)
                    identity = ([f'      have expanded : {pre} = {expanded_pre} := by',
                                 f'        simp only [{", ".join(parent_native)}]',
                                 '      exact expanded.trans (by ring)']
                                if parent_native else ['      ring'])
                    lines += [f'    have eq : {pre} = {expanded} := by', *identity, '    rw [eq]']
                    lines += ['    '+line for line in enclosure.proof(horner(step['pre']), Q(0), cap)]
                else:
                    if node.op in ('add', 'sub'):
                        lemma = 'abs_add_le' if node.op == 'add' else 'abs_sub'
                        lines += [f'    exact (({lemma} _ _).trans (add_le_add (native_bound b_{left}.bounds)',
                                  f'      (native_bound b_{right}.bounds))).trans (by norm_num)']
                    elif node.op == 'mul':
                        lines += [f'    exact (abs_product (native_bound b_{left}.bounds)',
                                  f'      (native_bound b_{right}.bounds)).trans (by norm_num)']
                    elif node.op == 'fma':
                        lines += [f'    exact ((abs_add_le _ _).trans (add_le_add',
                                  f'      (abs_product (native_bound b_{left}.bounds) (native_bound b_{right}.bounds))',
                                  f'      (native_bound b_{tail[0]}.bounds))).trans (by norm_num)']
                    else:
                        den = summaries[right]
                        lines += [f'    have low : {real(den.c-den.w)} ≤ value {right} := by',
                                  f'      linarith only [(abs_le.mp b_{right}.bounds.centre).1]',
                                  f'    exact (abs_div_upper (native_bound b_{left}.bounds) (by norm_num) low).trans (by norm_num)']
                if step['zero']:
                    lines += [f'  have q_{name} := Flare.Binary64.Zero.add_right_zero _ _ b_{left}.finite b_{right}.finite',
                              f'    (by linarith only [(abs_le.mp b_{right}.bounds.centre).1, (abs_le.mp b_{right}.bounds.centre).2])',
                              f'  have r_{name} : |value {name} - {pre}| ≤ {real(rho)} := by',
                              f'    have hz : value {right} = 0 := by linarith only [(abs_le.mp b_{right}.bounds.centre).1, (abs_le.mp b_{right}.bounds.centre).2]',
                              f'    rw [q_{name}.2, hz]; simp']
                else:
                    divisor = ''
                    if node.op == 'div':
                        divisor = f' (by have h := (abs_le.mp b_{right}.bounds.centre).1; intro hz; rw [hz] at h; norm_num at h)'
                    operands = ('_ _ _ '+f'b_{left}.finite b_{right}.finite b_{tail[0]}.finite' if node.op == 'fma'
                                else f'_ _ b_{left}.finite b_{right}.finite')
                    lines += [f'  have q_{name} := Flare.Binary64.Nearest.{node.op}_error_nearest '+operands+divisor,
                              f'    (m_{name}.trans (by norm_num))',
                              f'  have r_{name} : |value {name} - {pre}| ≤ {real(rho)} := by',
                              f'    apply q_{name}.2.trans',
                              '    calc',
                              f'      _ ≤ (2 : ℝ)^(-53 : Int) * ({real(cap)} + (2 : ℝ)^(-1022 : Int)) :=',
                              f'        mul_le_mul_of_nonneg_left (add_le_add m_{name} le_rfl) (by norm_num)',
                              '      _ ≤ _ := by norm_num']
                if step['native'] is not None:
                    delta = 'd'+name[1:]
                    lines += [f'  let {delta} : ℝ := value {name} - {pre}',
                              f'  have {delta}_lo := (abs_le.mp r_{name}).1', f'  have {delta}_hi := (abs_le.mp r_{name}).2',
                              f'  change -{real(rho)} ≤ {delta} at {delta}_lo',
                              f'  change {delta} ≤ {real(rho)} at {delta}_hi',
                              f'  have p_{name} : value {name} = {render(horner(step["native"]))} := by',
                              f'    conv_rhs => dsimp only [{delta}]',
                              *([f'    conv_rhs => simp only [{", ".join(parent_native)}]'] if parent_native else []), '    ring',
                              f'  clear_value {delta}',
                              *['  '+line for line in enclosure.atom(delta, -rho, rho, delta)],
                              f'  have j_{name} : {ideal_name} = {render(horner(step["ideal"]))} := by',
                              '    ring!',
                              f'  have b_{name} : {target} := by', f'    refine ⟨q_{name}.1, ?_, ?_, ?_⟩',
                              f'    · rw [p_{name}]',
                              *['      '+line for line in enclosure.proof(horner(step['native']), b.c, b.w)],
                              f'    · rw [j_{name}]',
                              *['      '+line for line in enclosure.proof(horner(step['ideal']), Q(0), b.i)],
                              f'    · rw [p_{name}, j_{name}]',
                              f'      have eq : {render(horner(step["native"]))} - {render(horner(step["ideal"]))} = {render(horner(add(step["native"], step["ideal"], -1)))} := by ring',
                              '      rw [eq]',
                              *['      '+line for line in enclosure.proof(horner(add(step['native'], step['ideal'], -1)), Q(0), b.e)]]
                else:
                    operands = f'b_{left}.bounds b_{right}.bounds'
                    if node.op == 'div':
                        operands += ' (by norm_num) (by norm_num)'
                    bounds = (f'add_bounds (mul_bounds {operands}) b_{tail[0]}.bounds' if node.op == 'fma'
                              else f'{node.op}_bounds {operands}')
                    lines += [f'  have raw_{name} := rounded ({bounds}) r_{name}',
                              f'  have b_{name} : {target} := ⟨q_{name}.1, weaken raw_{name}',
                              '    (by norm_num) (by norm_num) (by norm_num)⟩']
        terms = []
        for name in program.outputs:
            terms += [f'b_{name}.finite', f'b_{name}.bounds.error.trans (by norm_num : {real(summaries[name].e)} ≤ {rational_real(claims[name].e)})']
        lines += (finish(box) if finish is not None else ['  exact ⟨'+', '.join(terms)+'⟩'])+['']
    lines += [f'theorem accuracy {params(program)}', *['    '+h for h in hypotheses(program, root['domain'])],
              '    : '+(goal or proposition(program, claims))+' := by']
    def branch(box, depth=0, tests=()):
        nonlocal lines
        prefix = '  '+'  '*depth
        if 'split' in box:
            index, mid, children = box['split']
            label = 's'+str(depth)
            lines.append(prefix+f'by_cases {label} : value a{index} ≤ {real(mid)}')
            for child in children:
                lines.append(prefix+'·')
                branch(child, depth+1, (*tests, label))
        else:
            index = next(i for i, leaf in enumerate(leaves) if leaf is box)
            lines.append(prefix+f'apply box_{index} {args}')
            for i, _ in enumerate(program.inputs):
                facts = ', '.join([f'h{i}.2.1', f'h{i}.2.2', *tests])
                lines += [prefix+f'· exact ⟨h{i}.1, by linarith only [{facts}], by linarith only [{facts}]⟩']
    branch(root)
    return '\n'.join([*lines, '', 'end Workflow.Scalar', ''])


def proposal(program, request, candidates=None, details=None):
    if not supported(program):
        raise ValueError('Reusable scalar inference admits at most '+str(MAX_OPERATIONS)+' IR nodes')
    limits = list(map(Q, candidates)) if candidates is not None else [Q(t['limit']) for t in request['outputs']]
    if len(limits) != len(program.outputs) or any(limit < 0 for limit in limits):
        raise ValueError('Expected one nonnegative scalar candidate per output')
    try:
        root, leaves = plan(program, request['domain'], limits)
    except ValueError:
        from numerics.analysis import checked_bounds
        if checked_bounds.supported(program):
            return checked_bounds.proposal(program, request, candidates, details)
        raise
    summaries = dict(root['summaries'])
    for name in program.outputs:
        summaries[name] = replace(summaries[name], e=max(box['summaries'][name].e for box in leaves))
    claims = {name: replace(summaries[name], e=(limits[index] if candidates is not None else
              max(box['summaries'][name].e for box in leaves))) for index,name in enumerate(program.outputs)}
    metadata = {**(details or {}), 'validation': 'lean-scalar-interval-v1',
                'claim_policy': 'producer-output-claims' if candidates is not None else 'checked-scalar-inference',
                'boxes': len(leaves), 'foreign_trace_checked': False,
                'rule_checker': enclosure.CHECKER, 'enclosure_rules': enclosure.RULES,
                'qualification': 'Candidate bounds and polynomial rewrites are checked against native Float laws in Lean.'}
    if program.precision:
        metadata['primitive_rules']=['Flare.Binary32.StorageBounds.native_roundTrip',
            'Flare.Binary32.Conversion.widen_exact','Flare.FloatFormat.Rounding.round_direct_error']
    from numerics.analysis.square_root import evidence as root_evidence
    if program.math and 'sqrt' in program.math['operations']:
        metadata['primitive_rules']=['Flare.Binary64.SqrtPropagation.native_sqrt',
            'Flare.Analysis.SqrtBounds.difference_le_of_floor','Flare.Analysis.SqrtBounds.difference_le_of_sq']
    steps = [{'box': index, 'domain': box['domain'],
              'nodes': [{'node': step['node'].name, 'op': step['node'].op,
                         'rounding_allowance': str(step['rho']), 'pre_rounding_magnitude': str(step['magnitude']),
                         'summary': step['bound'].record(),
                         **({'storage_exponent':step['storage_exponent']} if 'storage_exponent' in step else {}),
                         **({'sqrt':root_evidence(step['sqrt'])} if 'sqrt' in step else {})} for step in box['steps']]} for index,box in enumerate(leaves)]
    return Proposal(summaries, steps, claims, metadata,
                    lean_source=proof_module(program, root, leaves, claims),
                    authored={'accuracy': 'Workflow.Scalar.accuracy'})
