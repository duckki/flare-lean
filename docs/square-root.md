# Verify square-root applications

The restricted Python math profile certifies explicit `math.sqrt` calls, optionally
combined with `math.fma` and ordinary scalar operations. It checks input domains,
incoming errors, native square-root rounding and later operations in one Lean
root. The [retained applications](../examples/numerics/sqrt/README.md) include
standard deviation, regularized norms and a normalized residual.

## Select the source and primitive contract

Use CPython 3.13 or 3.14 and `python_math: true` in the request. Inspect an actual
function before supplying independent specifications and engineering limits:

```sh
python3 scripts/certify_numerics.py inspect --language python \
  --source examples/numerics/sqrt/kernels.py \
  --function normalized_residual --python-math
python3 scripts/certify_numerics.py run \
  --request examples/numerics/sqrt/normalized_residual.json \
  --out .cache/numerics-generated/normalized-residual
python3 scripts/certify_numerics.py replay \
  --run .cache/numerics-generated/normalized-residual \
  --out .cache/numerics-generated/normalized-residual-replay
```

These are ignored provider regression destinations. Confirm the verification
location for an application and put scratch under its agreed `.cache/` directory.

The profile requires one unaliased `import math` and unshadowed positional calls.
Scalar helpers and bounded literal-tuple loops keep their original operation
order. At most 32 graph nodes and one or two scalar outputs are admitted. No
implicit FMA, reassociation, cast or dtype change is introduced. Use `sqrt(expr)`
in the independent exact-reference DSL; it denotes `Real.sqrt`, rather than a
second execution of `math.sqrt`.

The frozen arithmetic model extends ordinary binary64 nearest/even arithmetic:

```json
{
  "format": "binary64",
  "rounding": "nearest-even",
  "subnormals": "gradual",
  "fma": false,
  "reassociation": false,
  "functions": {"sqrt": "ieee754-binary64-nearest-even"}
}
```

With explicit source FMA calls, `fma` becomes `"explicit"`. FMA-only graphs keep
their previous schema, model and replay identities. An explicitly supplied model
must match the selected graph, including the function contract. One-ulp libm
models, other formats and rounding modes are not interchangeable with this one.

## What Lean checks

FLARE already proves `Binary64.Sqrt.sqrt_error_nearest` for the actual Lean 4.35
`Float.sqrt` model: a finite nonnegative operand has a finite square root whose
error from its exact real root is at most `2⁻⁵³ * sqrt(operand)`. The proof covers
signed zero and positive subnormals, following integer-root and nearest rounding.

`Binary64.SqrtPropagation.native_sqrt` composes that result with checked root
ranges and perturbation allowances. Endpoint proposals use exact rational
arithmetic and Python's integer `isqrt`, without host floating-point square root.
Lean proves their squared inequalities and the original variable bounds.

Incoming error is discharged by reusable pure-real rules in `Analysis.SqrtBounds`:

- A common positive root floor `l` gives
  `|sqrt(n) - sqrt(i)| ≤ |n-i| / (2*l)`.
- Without a positive floor, a checked `|n-i| ≤ d²`, with `d ≥ 0`, gives
  `|sqrt(n) - sqrt(i)| ≤ d`. This remains valid at zero.

The checker proves nonnegative **native and exact** arguments. It retains native
root nonnegativity for nested roots and carries accumulated error into later
operations; a square root never resets the reference to an already rounded value.
The final theorem compares against the independent exact specification and checks
the engineering budget. Its transitive axioms remain the standard project allowlist.

Exact-reference comparison uses checked primitive congruence and ring proofs.
More general functional identities can need an additional proof route. This is
separate from establishing a numerical allowance.

## Examples and limits

All five application requests certify and cold-replay. The direct variance case
includes zero, either zero sign and subnormal diagnostic inputs. A nested-root
case uses the zero-inclusive perturbation rule; its checked allowance is about
`2.11e-8`, within its retained `1e-6` requirement. That rule is intentionally
coarser near zero than the positive-floor rule.

The same standard-deviation source with a `2⁻⁶⁰` requirement has a checked
`budget_not_met` result. An upper allowance above budget is not a counterexample.
A domain containing negative variance remains unresolved at domain inference;
it does not become a claim about Python's exception-raising execution.

A conservative range that crosses zero can also need stronger reasoning even
when the actual argument is nonnegative. In particular, this profile does not
claim to automatically close every unregularized sum of rounded squares around
zero. Keep the source, reference and requirement fixed while resolving that gap.

Lean rejects corrupted root endpoints, lost incoming error, a substituted native
primitive and a false independent reference. Other controls reject incompatible
formats/function contracts, unsupported calls and runtime versions. The provider
also tests zero, a subnormal-only domain and rational interval endpoints.

## Runtime boundary and frozen replay

[CPython's math API](https://docs.python.org/3.14/library/math.html#math.sqrt)
describes the source function. The inspected
[CPython 3.14.7 implementation](https://github.com/python/cpython/blob/v3.14.7/Modules/mathmodule.c)
wraps the platform C `sqrt`; Lean's native primitive also names C `sqrt`. Mapping
that implementation to the declared IEEE nearest/even contract remains an explicit
runtime/libm/hardware assumption. FLARE does not prove CPython or the C library.
The Python API alone does not prove this implementation contract.

Admission records the actual Python version, executable and loaded `math`
extension hashes, plus OS/kernel/architecture and macOS/libc version metadata.
Selected sqrt and subnormal probes and original-source/IR word comparisons are
sampled diagnostics. They are not universal correctly-rounded implementation
proofs or a complete fingerprint of all dynamically linked platform libraries.

A live freshness audit checks these recorded identities and platform metadata.
Frozen replay rechecks the source-derived Lean model, saved numerical theorem
and axiom closure without running CPython, the analyzers or inference. It does not
revalidate a changed runtime implementation.

Use `lean-flare` and Lean delivery for this profile. External-producer function
models, Rust extraction, binary32 and arbitrary composition with other source
profiles need their own bridges; installing a tool does not supply them.
