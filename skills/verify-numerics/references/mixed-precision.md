# Binary32 storage and binary64 computation

Select `python_mixed: true` for ordinary scalar Python functions containing
explicit `float(np.float32(x))` pairs and exactly `import numpy as np`. Parameters,
ordinary arithmetic and returned values remain binary64. A pair narrows to
binary32 nearest/even with gradual subnormals and promotes exactly back to
binary64. It may appear before or after arithmetic, including through helpers.

Use CPython 3.13/3.14 and NumPy 2.4.0. Obtain missing compatible tools in the shared
pool using [tool-setup.md](tool-setup.md), preserving application configuration.
Run `inspect --python-mixed` and retain original domains, units, budgets and an
independent exact reference on the original inputs. Do not reset that reference
to a stored/rounded intermediate or silently remove a conversion.

The Lean model uses explicit model-backed conversion functions because the pinned
Lean width-conversion built-ins are opaque. Shared format inference checks the
narrowing allowance; widening is proved exact for all finite binary32 values.
The provider adds storage error to incoming error at each conversion. A checked
storage magnitude at most `2^126` proves finiteness; gradual underflow is covered.
The one-ulp allowance can be conservative near zero.

This source profile has at most 32 nodes and one or two scalar outputs. Unpaired
casts, binary32 arithmetic, implicit NumPy promotions, other dtypes and arbitrary
profile composition need separate bridges. Use `lean-flare` and Lean delivery;
external-producer and Rust routes do not yet supply the required cast bridges.

Runtime/library hashes and platform metadata bind diagnostics to the selected
NumPy implementation. Sampled word/probe checks do not prove NumPy, CPython or
compiler/hardware correctness. Frozen replay reparses source and rechecks Lean
without loading NumPy or running inference. An allowance above budget is not a
counterexample.

See [the profile guide](../../../docs/arithmetic/mixed-precision.md) and
[maintained applications](../../../examples/numerics/mixed/README.md) for exact
contracts, limits and reproducible commands. Application output locations follow
the confirmed verification directory, with scratch beneath its `.cache/`.
