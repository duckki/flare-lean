"""Emit operation-ordered implementations and checker obligations from the common IR."""
from fractions import Fraction as Q
from collections import Counter
import re

from .frontend import number
from .specification import lean_specification


def real(x):
    x = Q(x)
    return f"({x.numerator} : ℝ)" if x.denominator == 1 else f"(({x.numerator} : ℝ) / {x.denominator})"


def expression(node, ideal=False, rust=False):
    if node.op in ("select_lt", "select_le"):
        left, right, yes, no = node.args
        op = "<" if node.op == "select_lt" else "≤"
        if rust:
            op = "<" if node.op == "select_lt" else "<="
            return f"if {left} {op} {right} {{ {yes} }} else {{ {no} }}"
        return f"(if {left} {op} {right} then {yes} else {no})"
    if node.op == "constant":
        if ideal:
            return real(Q.from_float(number(node.bits)))
        return repr(number(node.bits)) if rust else f"Float.ofBits {node.bits}"
    if node.op == "neg":
        return f"(-{node.args[0]})"
    symbol = {"add": "+", "sub": "-", "mul": "*", "div": "/"}[node.op]
    return f"({node.args[0]} {symbol} {node.args[1]})"


def returned(outputs):
    return outputs[0] if len(outputs) == 1 else "(" + ", ".join(outputs) + ")"


def result_type(typ, count):
    return ' × '.join([typ]*count)


def projection(index, count):
    return '' if count == 1 else '.2'*index + ('.1' if index < count-1 else '')


def rust_source(program):
    params = ", ".join(f"a{i}: f64" for i in range(len(program.inputs)))
    result = "f64" if len(program.outputs) == 1 else "(f64, f64)"
    lines = ["// Generated from the frozen ordered-binary64 IR.", f"pub fn kernel({params}) -> {result} {{"]
    lines += [f"    let {n.name} = {expression(n, rust=True)};" for n in program.nodes]
    return "\n".join([*lines, "    " + returned(program.outputs), "}", ""])


def kernel_source(program, specification):
    result = []
    used={arg for node in program.nodes for arg in node.args} | set(program.outputs)
    for name, typ, ideal in [("kernel", "Float", False), ("reference", "ℝ", True)]:
        params = " ".join(f"(a{i} : {typ})" for i in range(len(program.inputs)))
        out = result_type(typ,len(program.outputs))
        declaration = 'noncomputable def' if ideal else 'def'
        result += [f"{declaration} {name} {params} : {out} :="]
        result += [f"  let {n.name if n.name in used else '_'+n.name} := {expression(n, ideal=ideal)}" for n in program.nodes]
        result += ["  " + returned(program.outputs), ""]
    arguments = ' '.join(f'(a{i} : ℝ)' for i in range(len(program.inputs)))
    output_type = result_type('ℝ',len(program.outputs))
    result += [f'noncomputable def specification {arguments} : {output_type} :=',
               *['  '+line for line in lean_specification(specification,program)], '']
    imports = ['public import Flare.Binary64.Value']
    if program.arrays:
        imports += ['public import Flare.Matrix.OrderedProduct','public import Mathlib.LinearAlgebra.Matrix.Notation']
    return "\n".join(["module", "", *imports, "", "@[expose] public section", "", "namespace Workflow", "", *result, "end Workflow", ""])


def params(program):
    return " ".join(f"(a{i} : Float)" for i in range(len(program.inputs)))


def applied(program):
    return " ".join(f"a{i}" for i in range(len(program.inputs)))


def hypotheses(program, domain):
    return [f"(h{i} : a{i}.isFinite = true ∧ {real(domain[name][0])} ≤ value a{i} ∧ value a{i} ≤ {real(domain[name][1])})"
            for i, name in enumerate(program.inputs)]


def proposition(program, summaries, output="kernel", exact="reference"):
    args = applied(program)
    refargs = " ".join(f"(value a{i})" for i in range(len(program.inputs)))
    clauses = []
    for i, node in enumerate(program.outputs):
        suffix = projection(i,len(program.outputs))
        native = f"output{suffix}" if output == 'output' else f"({output} {args}){suffix}"
        ideal = f"({exact} {refargs}){suffix}"
        clauses += [f"{native}.isFinite = true", f"|value {native} - {ideal}| ≤ {real(summaries[node].e)}"]
    return "\n      ∧ ".join(clauses)


def bound_derivation(program, summaries, steps, ideal_inputs=None):
    lines = []
    uses=Counter(x for node in program.nodes for x in node.args)
    uses.update(program.outputs)
    for node, step in zip(program.nodes, steps, strict=True):
        b = summaries[node.name]
        ideal_name = "i" + node.name[1:]
        native_expr = expression(node)
        ideal_expr = expression(node, ideal=True)
        ideal_expr = re.sub(r'\b[an]\d+\b', lambda m: (ideal_inputs or {}).get(m[0], f"(value {m[0]})") if m[0].startswith('a') else 'i'+m[0][1:], ideal_expr)
        lines += [f"  let {node.name} : Float := {native_expr}", f"  let {ideal_name} : ℝ := {ideal_expr}"]
        target = f"NativeBounds {real(b.c)} {real(b.w)} {real(b.i)} {real(b.e)} {node.name} {ideal_name}"
        if node.op == "constant":
            value = number(node.bits)
            bits = node.bits
            exponent = (bits >> 52) & 2047
            mantissa = bits & ((1 << 52)-1)
            if exponent:
                mantissa += 1 << 52
            power = exponent-1075 if exponent else -1074
            if bits >> 63:
                mantissa = -mantissa
            lines += [f"  have v_{node.name} : value {node.name} = {real(Q.from_float(value))} := by",
                f"    dsimp only [{node.name}]"]
            if value == 0:
                lines += ["    rfl"]
            else:
                lines += [f"    change ({mantissa} : ℝ) * (2 : ℝ) ^ ({power} : Int) = _", "    norm_num"]
            lines += [f"  have b_{node.name} : {target} := by",
                "    refine ⟨by decide +kernel, ?_, ?_, ?_⟩",
                f"    all_goals norm_num [{ideal_name}, v_{node.name}]"]
        elif node.op == "neg":
            lines += [f"  have b_{node.name} : {target} := by convert (native_neg b_{node.args[0]}) using 1; norm_num"]
        else:
            a, other = node.args
            op = node.op
            prefix = f"native_{op} b_{a} b_{other}"
            if op == "div":
                prefix += " (by norm_num) (by norm_num)"
            prefix += f" ({step['exponent']}) (by norm_num) (by norm_num)"
            lines += [f"  have raw_{node.name} := {prefix} (by"]
            if op in ("add", "sub"):
                lemma = "abs_add_le" if op == "add" else "abs_sub"
                lines += [f"    have bound := ({lemma} (value {a}) (value {other})).trans",
                    f"      (add_le_add (native_bound b_{a}.bounds) (native_bound b_{other}.bounds))"]
            elif op == "mul":
                lines += [f"    have bound := abs_product (native_bound b_{a}.bounds) (native_bound b_{other}.bounds)"]
            else:
                den = summaries[other]
                lines += [f"    have lower : {real(den.c-den.w)} ≤ value {other} := by",
                    f"      have h := (abs_le.mp b_{other}.bounds.centre).1", "      linarith only [h]",
                    f"    have bound := abs_div_upper (native_bound b_{a}.bounds) (by norm_num : (0 : ℝ) < {real(den.c-den.w)}) lower"]
            lines += ["    exact bound.trans (by norm_num))"]
            if step.get('ideal_refinement'):
                wide=f"NativeBounds {real(b.c)} {real(b.w)} {real(step['raw_ideal'])} {real(b.e)} {node.name} {ideal_name}"
                lines += [f"  have wide_{node.name} : {wide} := native_weaken raw_{node.name}",
                          "    (by norm_num) (by norm_num) (by norm_num)",
                          f"  have b_{node.name} : {target} := native_ideal_refine wide_{node.name} (by norm_num)"]
                lines += [f'  clear raw_{node.name} wide_{node.name}']
            else:
                lines += [f"  have b_{node.name} : {target} := native_weaken raw_{node.name}",
                          "    (by norm_num) (by norm_num) (by norm_num)"]
                lines += [f'  clear raw_{node.name}']
        for parent in node.args:
            uses[parent]-=1
            if uses[parent]==0:
                lines += [f'  clear b_{parent}']
    return lines


def proof_source(program, domain, summaries, steps, targets, with_rust=False, authored=None, folded=False, rust_equivalence=None, claims=None):
    args = applied(program)
    hyps = hypotheses(program, domain)
    conclusion = {**summaries, **(claims or {})}
    imports = ['module', '', 'public import Workflow.Kernel',
        'public import Flare.Binary64.Pipeline']
    if with_rust:
        imports.append('public import Workflow.Generated.Funs')
    if rust_equivalence:
        imports.append('public import Workflow.RustEquiv')
    if authored:
        imports.append('public import Workflow.Authored')
    lines = [*imports, 'meta import Lean.Util.CollectAxioms', '',
        '@[expose] public section', '', 'namespace Workflow.Certificate', '',
        'open Flare.Binary64.Pipeline Flare.Binary64.Value', '',
        'set_option maxHeartbeats 2000000', 'set_option maxRecDepth 4096', '',
        f'theorem accuracy {params(program)}', *['    '+h for h in hyps],
        '    : '+proposition(program, conclusion)+' := by']
    if authored:
        lines += ['  exact '+authored['accuracy']+' '+args+' '+
                  ' '.join(f'h{i}' for i in range(len(program.inputs)))]
    else:
        for i, name in enumerate(program.inputs):
            b = summaries[f"a{i}"]
            lines += [f"  have b_a{i} : NativeBounds {real(b.c)} {real(b.w)} {real(b.i)} 0 a{i} (value a{i}) := by",
                f"    apply same _ _ _ _ h{i}.1",
                f"    · rw [abs_le]; constructor <;> linarith only [h{i}.2.1, h{i}.2.2]",
                f"    · rw [abs_le]; constructor <;> linarith only [h{i}.2.1, h{i}.2.2]"]
        lines += bound_derivation(program, summaries, steps)
    if not authored:
        terms = []
        for node in program.outputs:
            error = f"b_{node}.bounds.error"
            if claims is not None:
                error = '('+error+').trans (by norm_num : '+real(summaries[node].e)+' ≤ '+real(conclusion[node].e)+')'
            terms += [f"b_{node}.finite", error]
        lines += ["  exact ⟨" + ", ".join(terms) + "⟩"]
    lines += ['', 'theorem specification_equiv '+
        ' '.join(f'(a{i} : ℝ)' for i in range(len(program.inputs))),
        f'    : reference {args} = specification {args} := by']
    if authored and authored.get('specification_equiv'):
        lines += ['  exact '+authored['specification_equiv']+' '+args]
    elif folded and not program.arrays:
        lines += ['  rfl']
    else:
        lines += ['  unfold reference specification']
        if program.arrays:
            lines += ['  simp [Matrix.mul_apply'+(', Fin.sum_univ_succ' if program.arrays['product'][1]>1 else '')+', Matrix.of_apply'+
                      (', add_assoc' if program.arrays['product'][1]>2 else '')+']']
        else:
            lines += ['  apply Prod.ext <;> ring' if len(program.outputs)>1 else '  ring']
    if with_rust:
        lines += ['', f'theorem source_equiv {params(program)}',
            f'    : Generated.kernel {args} = .ok (kernel {args}) := by',
            '  exact '+rust_equivalence+' '+args if rust_equivalence else '  rfl']
    meets = all(conclusion[n].e <= Q(t['limit'])
                for n,t in zip(program.outputs,targets,strict=True))
    budget = ' ∧ '.join(f'{real(conclusion[n].e)} ≤ {real(t["limit"])}'
                        for n,t in zip(program.outputs,targets,strict=True))
    clauses = proposition(program,conclusion,output='output' if with_rust else 'kernel',exact='specification')
    if meets:
        clauses += '\n      ∧ ('+budget+')'
    lines += ['', f'theorem certificate {params(program)}', *['    '+h for h in hyps]]
    if with_rust:
        lines += ['    : ∃ output,', f'        Generated.kernel {args} = .ok output',
                  '        ∧ '+clauses+' := by',
                  f'  refine ⟨kernel {args}, source_equiv {args}, ?_⟩']
    else:
        lines += ['    : '+clauses+' := by']
    accuracy='accuracy '+args+' '+' '.join(f'h{i}' for i in range(len(program.inputs)))
    if meets:
        # The finite/error clauses are right-associated; keep their proof intact
        # by using a separately typed conjunction before reassociation.
        lines += ['  have numerical : '+proposition(program,conclusion,exact='specification')+' := by',
                  '    rw [← specification_equiv]', '    exact '+accuracy,
                  '  have budget : '+budget+' := by norm_num',
                  '  exact ⟨'+', '.join('numerical'+projection(i,2*len(program.outputs))
                      for i in range(2*len(program.outputs)))+', budget⟩']
    else:
        lines += ['  rw [← specification_equiv]', '  exact '+accuracy]
    lines += ['', 'end Workflow.Certificate', '', 'open Lean in', 'run_cmd do',
        '  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]',
        '  for axiomName in ← Lean.collectAxioms ``Workflow.Certificate.certificate do',
        '    unless allowed.contains axiomName do',
        '      throwError "Unexpected axiom {axiomName} in root certificate"',
        '  logInfo "Lean root certificate checked; standard Lean foundations only."', '']
    text = "\n".join(lines)
    if program.arrays:
        from .array_emit import proof_source as array_proof_source
        text = text.replace('theorem certificate ', 'theorem scalar_certificate ').replace(
            '``Workflow.Certificate.certificate','``Workflow.Certificate.scalar_certificate')
        text += array_proof_source(program,domain,conclusion,targets)
    if program.c:
        from .c_emit import proof_source as c_proof_source
        text = text.replace('theorem certificate ', 'theorem scalar_certificate ').replace(
            '``Workflow.Certificate.certificate','``Workflow.Certificate.scalar_certificate')
        text += c_proof_source(program,domain,conclusion,targets,with_rust)
    return text


def check_source(program, domain, summaries, targets, with_rust=False):
    """Ascribe the root's independently reconstructed type and audit its axiom closure."""
    if program.c:
        from .c_emit import check_source as c_check_source
        return c_check_source(program,domain,summaries,targets,with_rust)
    if program.arrays:
        from .array_emit import check_source as array_check_source
        return array_check_source(program,domain,summaries,targets)
    args=applied(program)
    hyps=hypotheses(program,domain)
    clauses=proposition(program,summaries,output='output' if with_rust else 'kernel',exact='specification')
    if all(summaries[n].e<=Q(t['limit']) for n,t in zip(program.outputs,targets,strict=True)):
        budget=' ∧ '.join(f'{real(summaries[n].e)} ≤ {real(t["limit"])}'
                          for n,t in zip(program.outputs,targets,strict=True))
        clauses+='\n      ∧ ('+budget+')'
    if with_rust:
        clauses=f'∃ output, Generated.kernel {args} = .ok output ∧ '+clauses
    lines=['module','','import all Workflow.Proof','meta import Lean.Util.CollectAxioms','',
           'open Workflow Flare.Binary64.Value','',f'example {params(program)}',
           *['    '+h for h in hyps], '    : '+clauses+' :=',
           '  Workflow.Certificate.certificate '+args+' '+
           ' '.join(f'h{i}' for i in range(len(program.inputs))), '',
           'open Lean in','run_cmd do',
           '  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]',
           '  for axiomName in ← Lean.collectAxioms ``Workflow.Certificate.certificate do',
           '    unless allowed.contains axiomName do',
           '      throwError "Unexpected axiom {axiomName} in root certificate"',
           '  logInfo "Requested root type and transitive axioms checked independently."','']
    return '\n'.join(lines)
