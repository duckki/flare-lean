# Use FLARE as a Lean library

FLARE is one Lean proof library: repository `flare-lean`, Lake package `flare`,
namespace `Flare`. You can import its definitions and theorems without using
the agent skill or installing optional numerical-analysis/Rust extraction tools.

## Add the dependency

Use the same Lean toolchain as FLARE, currently `leanprover/lean4:v4.35.0`.
Add this dependency to your project's `lakefile.toml`, replacing the revision
placeholder with the full commit SHA you intend to use:

```toml
[[require]]
name = "flare"
git = "https://github.com/duckki/flare-lean.git"
rev = "<full FLARE commit SHA>"
```

For a `lakefile.lean` project, the equivalent declaration is:

```lean
require flare from git
  "https://github.com/duckki/flare-lean.git" @ "<full FLARE commit SHA>"
```

Then run from your project:

```sh
lake update flare
lake build
```

FLARE uses Mathlib v4.35.0. If your project already depends on Mathlib, align
the dependency revisions rather than combining incompatible versions. Commit
your Lake manifest to retain the resolved dependencies. See the
[development guide](development.md#shared-build-cache) for optional shared
artifact caching and bootstrapping missing Mathlib artifacts.

## Import and use theorems

Import the whole public library with `import Flare`, or use a focused module:

```lean
import Flare.Binary64.Nearest

#check Flare.Binary64.Nearest.add_error_nearest
#check Flare.Binary64.Nearest.div_error_nearest
```

Theorems retain explicit assumptions about finiteness, magnitudes, dimensions
and conditioning. Match those premises to your own implementation and input
domain before applying a result. Native `Float` operations and their real
interpretations are distinct; exceptional values and signed zero require the
stated interpretation rules.

Use the [theorem guide](reference.md) to find entry points and the
[organization guide](organization.md) for subject areas and dependency rules.
The Lean declarations give the complete contracts. A theorem about a Lean
algorithm does not by itself verify an unrelated Python, Rust or BLAS
implementation; that requires an explicit correspondence argument or the
separately scoped [application verification workflow](numerical-verification.md).
