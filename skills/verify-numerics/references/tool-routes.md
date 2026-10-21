# Choose a workflow by the obligation

Use the installed version's documentation and test its arithmetic semantics.
The choices below can be combined; they are not a ranking. This skill delivers
one Lean certificate. Other proof assistants remain useful comparison or
intermediate routes; use [lean-conversion.md](lean-conversion.md) to reconstruct
required numerical results in Lean before claiming workflow completion.

| Obligation | Useful routes | Check before using the result |
|---|---|---|
| Bounded straight-line arithmetic | Gappa, FPTaylor, or another admitted roundoff analyzer | Input interpretation, rounding sites, exceptional-value handling, actual certificate support and any input uncertainty. |
| Program verification conditions | Why3, Frama-C/WP, VST or a language-specific verified frontend | Which original language is translated; the IEEE versus real model; VC-generator/library trust; validity and memory obligations. |
| Composition, invariants, domain mathematics | Lean/Mathlib/FLARE, Coq/Flocq/VCFloat2/LAProof, PVS, or another suitable prover | Reusable lemmas, model match, caller-premise discharge, library axioms, source correspondence and ongoing maintenance cost. |
| Modular calls and unstable floating-point branches | PRECiSA/PVS or another demonstrated branch analyzer | Version-specific frontend, accumulated input errors, supported recursion/collections and certificate replay. General provers can express these goals too. |

Gappa is primarily an arithmetic prover. A frontend such as Why3 can generate
its verification conditions. User algebraic rewrite hypotheses in a generated
certificate still need proofs. Gappa/Coq can supply local bounds inside an
inductive or matrix proof; a flat timeout does not rule out composition.

FPTaylor supplies rigorous analyzer bounds in its supported models. Its output
word `exact` labels an optimization formulation, not an independently checked
certificate or an attained IEEE worst case. The pinned revision's formal
instructions below require v0.9.3 to record certificates and exclude the advanced
rounding model in that verification procedure. Verify the actual version/model's path rather than inheriting
a certificate claim from a paper or another release.

Check configuration semantics against the installed version, including option
units and applicability to the selected optimizer. A recorded option value is
not necessarily an effective resource limit. Preserve literal configuration
and enforced external process limits separately; an incoming task description
can contain a unit error. For proof replay, identify which modules and imports
each command checks. Grouping several modules under one timeout changes the
work per invocation; a timeout on that group does not establish that each
individual module is uncheckable.

A general prover is useful when obligations need mathematics, executable
contracts or composition that available analyzers do not supply automatically.
This is shared capability across proof assistants. Existing application and
floating-point libraries can dominate effort; their availability is a measured
context, not an intrinsic advantage of the prover's name.

Suggested primary references, when the corresponding route matters:

- [Gappa arithmetic-proof case study](https://guillaume.melquiond.fr/doc/10-tc.pdf).
- [FPTaylor method and evaluation](https://soarlab.org/papers/2018_toplas_sbbjrg.pdf)
  and the [studied revision's certificate instructions](https://github.com/soarlab/FPTaylor/blob/b5a77cae348400f21f83512210d9f43c4bffb381/formal/README.md).
- [PRECiSA 4.0 modular/branch analysis](https://shemesh.larc.nasa.gov/fm/papers/FM2024-draft.pdf).
- [VCFloat2](https://www.cs.princeton.edu/~appel/papers/vcfloat2.pdf) and
  [LAProof](https://www.cs.princeton.edu/~appel/papers/LAProof.pdf).
- [FPBench: common semantics and comparison measures](https://homes.cs.washington.edu/~ztatlock/pubs/fpbench-damouche-nsv16.pdf).

Failure recovery should address the observed obstacle: unavailable dependencies,
unsupported syntax, an invalid domain, lost correlations, insufficient search
budget, or an unproved source mapping. Record the obstacle before changing the
decomposition or configuration. A hybrid route may be the best engineering
choice even when no single analyzer closes every obligation. Combine their
search with Lean-checked local contracts and application composition, rather
than leaving foreign-checked numerical premises in the final Lean theorem.
