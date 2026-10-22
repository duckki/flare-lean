# FLARE

_**F**loating-point **L**ibrary for **A**rithmetic, **R**ounding, and **E**rror bounds._

**Numerical guarantees for your code, checked in [Lean](https://lean-lang.org/).**

Give your AI agent a function and an error budget or a property to preserve.
The skill can use FLARE, [Mathlib](https://leanprover-community.github.io/) and tools such as
**[Gappa](https://gappa.gitlabpages.inria.fr/), [FPTaylor](https://github.com/soarlab/FPTaylor)
and [PRECiSA](https://github.com/nasa/PRECiSA)**. **Lean** checks the resulting
proof or concrete counterexample; saved evidence lets you replay it.

Also, the skill can generate a verified Rust port;
**[Charon](https://aeneasverif.github.io/charon/)/[Aeneas](https://aeneasverif.github.io/)**
extracts its model for the correspondence proof in Lean.

**No skill installation is needed.** Use an agent with GitHub access and local
command execution. It [obtains FLARE and missing tools](skills/verify-numerics/references/tool-setup.md)
as needed.

## Example: verify a FilterPy function

### 1. Clone the demo

Clone [FilterPy](https://github.com/rlabbe/filterpy) at the revision used here:

```sh
git clone https://github.com/rlabbe/filterpy.git
cd filterpy
git checkout 3b51149ebcff0401ff1e10bf08ffca7b6bbc4a33
```

### 2. Ask your agent

Open the local checkout in your agent and paste:

```text
Read and follow the verification skill at:
https://github.com/duckki/flare-lean/blob/main/skills/verify-numerics/SKILL.md

Verify GHFilter.update in filterpy/gh/gh_filter.py with this contract:
- Use scalar Python floats, dt = 0.125 seconds, g = 0.5, h = 0.125.
- Omit per-call gain overrides.
- Run eight updates. Initial position is in [-10, 10] meters and initial
  velocity is in [-2, 2] meters/second. Each of the eight independent
  measurements is in [-10, 10] meters.
- Compare against an independent exact-real recurrence on the original inputs.
- Require final absolute error at most 1e-6 meters for position and
  1e-6 meters/second for velocity.
- Put verification artifacts in verification/.
```

### 3. Read the result

The tested run produced a certificate and passed saved-proof replay:

```text
# Numerical verification: certified

Lean entry: `Workflow.Certificate.certificate`.
```

| Output after eight updates | Checked error bound, rounded up | Requested budget |
| --- | --- | --- |
| Position | `2.44e-11` meters | `1e-6` meters |
| Velocity | `3.83e-11` meters/second | `1e-6` meters/second |

This covers arithmetic error under the stated conditions. It does not establish
physical tracking accuracy or cover arrays and arbitrary numbers of updates.
See [the workflow guide](docs/numerical-verification.md#filterpy-example) for
exact bounds and the source/runtime assumptions.

### Optional: generate Rust

Continue in the same session:

```text
Generate a reusable Rust port of this GHFilter API in rust/ and verify it
against the same eight-update contract. Keep verification evidence in
verification/.
```

The port includes the constructor, update method and state. A separate loop
driver covers the eight-update proof. The tested Rust port met the same bounds
and passed replay; its extracted model is also checked in Lean.

## Negative example: a Kalman update loses positive variance

Save this as `naive_covariance.py` in any project:

```python
def posterior_variance(p: float, r: float):
    gain = p / (p + r)
    return (1.0 - gain) * p
```

Here `p` is the prior variance and `r` is the measurement-noise variance.
Both are positive, so the exact posterior `p * r / (p + r)` must be positive.
Ask your agent to check that property:

```text
Read and follow the verification skill at:
https://github.com/duckki/flare-lean/blob/main/skills/verify-numerics/SKILL.md

Verify posterior_variance in naive_covariance.py with this contract:
- Use scalar Python floats: p in [1, 2] and r in [2^-54, 2^-53], both in
  square meters.
- Compare against the exact-real posterior p * r / (p + r) on the original inputs.
- Require a strictly positive result.
- Put verification artifacts in verification/naive-covariance/.
```

Expected engineering report, backed by a saved Lean proof:

```text
Outcome: counterexample proved
Inputs: p = 1, r = 2^-54
Binary64 posterior: 0
Exact posterior: 1 / (2^54 + 1) > 0
Requirement: strictly positive variance — violated
Lean entry: NaiveCovarianceFailure.failure
```

`p + r` rounds to `1`, so the gain becomes `1` and the returned variance is
zero. This is a concrete loss of positivity. The
[maintained counterexample](docs/numerical-verification.md#kalman-counterexample)
checks the input, native result and exact reference in Lean, then replays the
proof.

## Check the evidence

[Download and replay the example proofs](docs/numerical-verification.md#replay-the-readme-examples)
from a successful [Lean CI run](https://github.com/duckki/flare-lean/actions/workflows/ci.yml).
The `readme-evidence` artifact contains the FilterPy certificate and the Kalman
counterexample, with source, assumptions and commands. One replay command checks both.

## Try your own code

Use this prompt in your project, filling in the contract:

```text
Read and follow the verification skill at:
https://github.com/duckki/flare-lean/blob/main/skills/verify-numerics/SKILL.md

Verify <function> in <file> with this contract:
- Inputs: <numeric types, ranges and units>.
- Reference: <intended mathematical computation>.
- Requirement: <error budget or property to preserve>.
Confirm the verification and optional Rust output directories before creating files.
```

## What you receive

The report distinguishes three outcomes:

| Outcome | Meaning |
| --- | --- |
| **Requirement proved** | A Lean proof establishes your contract under the stated assumptions. |
| **Counterexample proved** | A Lean proof exhibits an allowed input that violates your requirement. |
| **Unresolved** | No proof or refutation yet; the report explains the remaining obstacle. |

An insufficient error bound leaves the requirement unresolved; it does not prove a bug.

The verification artifact directory contains:

- A report with the outcome, checked results and any remaining obligations.
- The source, input assumptions, exact reference and Lean proof evidence.
- Commands to reproduce the run and replay the saved proof.

Scratch work stays under that directory's `.cache/`.

## Optional installation

Install for reuse across tasks, so you can invoke `$verify-numerics` in Codex
instead of including the full URL.

With Node.js 22.20+ and Git, run:

```sh
npx skills add duckki/flare-lean --skill verify-numerics -g
```

Choose your agent when prompted, or add `--agent codex`. `-g` installs across
projects; omit it to install only in the current project.
See the [skills CLI](https://github.com/vercel-labs/skills) for other agents.

Alternatively, ask Codex's built-in
[$skill-installer](https://learn.chatgpt.com/docs/build-skills#install-curated-skills-for-local-use):

```text
Use $skill-installer to install skills/verify-numerics from duckki/flare-lean.
```

## Documentation

- [Development: build, format and test](docs/development.md)
- [Use FLARE as a Lean library](docs/using-library.md)
- [Proved results, organization and attribution](docs/organization.md)
- [Theorem reference](docs/reference.md)
- [Verification workflow and limitations](docs/numerical-verification.md)
- [Benchmarks](benchmarks/numerics/README.md)
- [Contributing](CONTRIBUTING.md)

[GPL-3.0-only](LICENSE). Third-party dependencies retain their own licenses.
