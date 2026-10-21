# FLARE

_**F**loating-point **L**ibrary for **A**rithmetic, **R**ounding, and **E**rror bounds._

**Verify numerical code with an AI agent and Lean. Optionally produce a verified Rust port.**

FLARE's `verify-numerics` agent skill checks floating-point error against an
exact mathematical reference and your engineering budget. Its Lean proof
library supplies reusable arithmetic and numerical-analysis theorems. A report
states the checked guarantee, its assumptions and any remaining gaps.

## Install the skill

With Node.js 22.20+ and Git available, install from GitHub using the
[skills CLI](https://github.com/vercel-labs/skills):

```sh
npx skills add duckki/flare-lean --skill verify-numerics -g
```

Select your agent when prompted, or add `--agent codex` (or another supported
agent). `-g` makes the skill available across projects; omit it to install in
the current project. No separate registry registration is required. The GitHub
source must contain the published `skills/verify-numerics/` directory.

In Codex, you can also ask its built-in
[$skill-installer](https://learn.chatgpt.com/docs/build-skills#install-curated-skills-for-local-use):

```text
Use $skill-installer to install skills/verify-numerics from duckki/flare-lean.
```

You can start without Lean or Rust installed. The skill directs the agent to
obtain the FLARE provider checkout and compatible tools, build the provider
and run preflight checks. Python 3.10+ is required by the provider. Reusable
tools go in a shared user cache outside your application checkout; setup can
require downloads and source builds. Actual network and installation permissions
still apply. See [tool setup](skills/verify-numerics/references/tool-setup.md)
for the supported route.

## Example: verify a FilterPy function

Clone [FilterPy](https://github.com/rlabbe/filterpy) and select the revision used
for this example:

```sh
git clone https://github.com/rlabbe/filterpy.git
cd filterpy
git checkout 3b51149ebcff0401ff1e10bf08ffca7b6bbc4a33
```

Open that local checkout in your AI agent and enter:

```text
Use $verify-numerics to verify GHFilter.update in filterpy/gh/gh_filter.py.
Use scalar Python floats, dt = 0.125 seconds, g = 0.5, h = 0.125, and no
per-call gain overrides. Verify eight consecutive updates, with initial
position in [-10, 10] meters, initial velocity in [-2, 2] meters/second,
and eight independent measurements each in [-10, 10] meters.
Compare against an independently stated exact-real recurrence on the original
inputs. Require final absolute errors at most 1e-6 meters for position and
1e-6 meters/second for velocity. Put verification artifacts in verification/.
```

The agent inspects the actual method, states the reference and domain, checks
the numerical proof in Lean, and replays the saved proof. The verification path
is supplied in the query; disposable work belongs in
`verification/.cache/`. For other tasks, the agent asks for missing ranges,
units, budgets and artifact locations before proceeding.

### Expected report

The exercised scalar example produced this excerpt from `report.md`:

```text
# Numerical verification: certified

Lean entry: `Workflow.Certificate.certificate`.

Selected Python method: `GHFilter.update`.

Allowances:
- position: checked 857/35184372088832 m; requested 1/1000000; meets budget: True.
- velocity: checked 673/17592186044416 m/s; requested 1/1000000; meets budget: True.
```

These allowances are about `2.44e-11` meters and `3.83e-11` meters/second.
The guarantee covers arithmetic error over the stated eight calls. The full
engineering report records source identity, the exact recurrence, assumptions and replay
commands. It assumes ordinary scalar instances with the configured fields;
Python construction and dispatch, runtime/hardware fidelity, and physical
tracking accuracy remain outside the numerical theorem. Arrays and arbitrary
call horizons are outside this example's scope.

### Optional: generate Rust

Continue in the same agent session:

```text
Generate a reusable Rust port of this GHFilter API in rust/ and verify it
against the same eight-update contract. Keep verification evidence in
verification/.
```

The skill preserves state, initialization, optional gain overrides and mutation
order. A separate verification driver calls the real API in a loop. The agent
obtains the pinned Rust extraction tools, proves the freshly extracted return
relation in Lean, and tests API/state behavior. The exercised Rust case retained
the same checked allowances and passed saved-proof replay. Charon/Aeneas's
translation and Float model are additional declared trust boundaries.

## Negative example: the requested budget is not met

Save this as `mean_update.py` in any project:

```python
def update(x: float, z: float, k: float):
    r = z - x
    m = r * k
    a = m + 0.0
    return a + x
```

Then ask your agent:

```text
Use $verify-numerics to verify update in mean_update.py with the default Lean
backend. Use finite scalar Python floats: x in [-1, 1] meters, z in
[-1/2, 1/2] meters, and dimensionless k in [0, 1]. Name the return updated_mean
and compare it against the exact-real expression x + k * (z - x) on the
original inputs. Require absolute error at most 2^-51 meters. Preserve the
source and requested budget. Put artifacts in verification/mean-update-tight
and report whether the checked allowance meets the requirement.
```

For this code, domain and budget, the current automatic backend reports:

```text
# Numerical verification: budget_not_met

Lean entry: `Workflow.Certificate.certificate`.

Allowances:
- updated_mean: checked 1/8796093022208 m; requested 1/2251799813685248; meets budget: False.
```

The checked allowance is `2^-43` meters; the requested budget is `2^-51`
meters. The workflow has not established the requested guarantee. An upper
bound above budget does not prove that the code attains that error; a tighter
proof may still succeed. A missing tool, unsupported construct, timeout or
proof failure instead leaves the run `unresolved`, with its failing stage
and logs retained.

## Review the delivery

Expect an engineering report, frozen source/request/proof evidence, checked
allowances versus your budgets, and reproducible run/replay commands under
the agreed verification directory. Supplemental reports stay outside sealed
run directories. Sampled runtime checks help diagnose source/model mismatches;
they do not replace the Lean proof. Freshness auditing checks identities;
saved-proof replay checks the mathematics again.

## Documentation

- [Development: build, format, check and test FLARE](docs/development.md)
- [Use FLARE as a Lean library](docs/using-library.md)
- [Proved results, repository organization and source attribution](docs/organization.md)
- [Theorem guide and assurance boundaries](docs/reference.md)
- [Numerical workflow, CLI and current capability limits](docs/numerical-verification.md)
- [Maintained workflow benchmarks](benchmarks/numerics/README.md)
- [Contributing](CONTRIBUTING.md) and [potential Mathlib contributions](docs/upstream/mathlib.md)
- [License: GPL-3.0-only](LICENSE); third-party dependencies retain their own licenses.
