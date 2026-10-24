# Obtain and configure verification tools

Use this when a required executable, runtime or compiled proof model is absent.
Download or build it with the agent's tools rather than asking the engineer to
perform routine installation. A missing entry on `PATH` is a setup task, not a
reason to stop verification immediately. Install only tools needed for the
selected route; external analyzers do not acquire a Lean importer merely by
being installed.

## Locations and identities

First reuse an explicitly configured compatible installation. Otherwise choose
a shared user-cache location outside the application and FLARE checkouts, such
as `~/Library/Caches/flare/` on macOS or `${XDG_CACHE_HOME:-$HOME/.cache}/flare/`
on Linux, or a user-specified tool pool. Announce the selected location. Key
installations by source revisions, OS/architecture and relevant Lean/Rust
toolchains so incompatible versions can coexist. Put application-specific
preflights and experiments under the agreed verification directory's `.cache/`.

Fetch from the tool's authoritative source/distribution. Prefer a release asset
only when it matches the required version, platform and arithmetic features;
check published integrity information when available. Otherwise fetch the exact
source revision and build it using that revision's documentation. Record source
URLs, commits or release identities, commands, logs, executable hashes and model
identities. A locally computed hash identifies a file; it does not prove its
upstream provenance. Do not relabel an unexamined binary as a pinned source build.

Keep installation in user scope and preserve existing toolchains. Use available
download, Git, package and compiler tools within the environment's permissions;
request a required execution escalation when access is blocked. Do not turn
upstream troubleshooting suggestions into unrequested system-wide removals or
configuration changes. If installation fails, retain the actual failed command
and try a compatible documented recovery before reporting the concrete blocker.

## Lean and the provider

GitHub/skills CLI installers can copy this skill without FLARE's Python CLI,
Lean sources or Lake project. Resolve any symlink, then check for those provider
files before treating an ancestor as `FLARE_ROOT`. An installer-managed skill
cache is not a complete provider checkout.

If only the application and skill are available, obtain the matching FLARE
source from [its repository](https://github.com/duckki/flare-lean) or a supplied
source bundle, under the shared user cache. Record the selected revision and
verify that it contains this skill and `scripts/certify_numerics.py`. A copied
skill does not imply that its provider is already installed. An unpublished
provider revision needs a supplied source bundle or publication before a
GitHub-only installation can reproduce it.

If Elan/Lake is absent, obtain Elan from its
[official distribution](https://github.com/leanprover/elan) using a user-scoped
installation. Install the Lean version in the provider's `lean-toolchain` and
build FLARE with that version; do not upgrade the application or create a new
application Lake project to satisfy tool setup. Preserve the user's shared Lake
artifact-pool configuration and leave `LAKE_CACHE_DIR` unset unless explicitly
configured. Missing Mathlib artifacts may need a one-time cache bootstrap as
described in [FLARE's development guide](https://github.com/duckki/flare-lean/blob/main/docs/development.md#shared-build-cache),
followed by a cache-enabled build;
ordinary checkouts should reuse the populated pool.

## Charon/Aeneas and its Lean model

Read `$FLARE_ROOT/tools/numerics/aeneas-revisions.json` for the authoritative
repository URLs, exact `aeneas.rev` / `charon.rev`, Lean toolchain and extraction
nightly. Read `tools/numerics/rust-toolchain.toml` for the separate Rust delivery
toolchain. The Float-enabled Aeneas fork is required; an unrelated upstream
release or the current branch head is not an equivalent replacement.

The supported source setup uses the pinned repositories' own build instructions:

- [Aeneas installation](https://github.com/duckki/aeneas/blob/9b10aaa080ba13e153af61e1c46b3ef457e3c302/README.md#installation--build)
  and [Make targets](https://github.com/duckki/aeneas/blob/9b10aaa080ba13e153af61e1c46b3ef457e3c302/Makefile).
- [Charon installation](https://github.com/AeneasVerif/charon/blob/de8736f7c995ac54dc490345cef9ea5143c06c62/README.md#installation--build)
  and its [compiler configuration](https://github.com/AeneasVerif/charon/blob/de8736f7c995ac54dc490345cef9ea5143c06c62/charon/rust-toolchain).

If the FLARE pins change, read the corresponding revisions' instructions rather
than treating these historical links as a second source of version selection.

1. Obtain Git, GNU Make, rustup and the OCaml/OPAM build prerequisites if missing,
   using their official distribution/install documentation. Fetch Aeneas into
   the shared tool pool and check out its exact recorded revision. Verify its
   `charon-pin` agrees with FLARE's Charon pin and its backend `lean-toolchain`
   agrees with FLARE before building.
   Apply the patches listed in `aeneas.patches` in the revision file before
   building. Verify each file's SHA-256, then run `git apply --check` and
   `git apply` with `$FLARE_ROOT/tools/numerics/u64-f64.patch` from the Aeneas
   checkout. This Lean-backend patch maps unsigned 64-bit casts to the existing
   native `UInt64.toFloat` model. It is needed by the integer-time application,
   and does not claim support for other floating-point casts. The complete IMU
   extraction/proof preflight exercises it; a scalar-only preflight does not.
2. Use an isolated OPAM switch for the tool build. The pinned Aeneas README uses
   OCaml 5 and gives 5.3.0 as an example. Initialize OPAM if necessary, install
   the switch and dependencies, then run the documented targets. For example,
   from the pinned Aeneas checkout, with `FLARE_MAKE` set to a GNU Make command
   (`gmake` on macOS installations where `make` is the older system version):

   ```sh
   opam switch create . 5.3.0 --no-switch --yes
   opam install --switch=. ./src --deps-only --with-test --yes
   opam exec --switch=. -- "$FLARE_MAKE" setup-charon
   opam exec --switch=. -- "$FLARE_MAKE"
   ```

   Reuse an already suitable switch instead of recreating it. `setup-charon`
   fetches/builds the matching Charon checkout; verify its actual revision after
   setup. Its rustup build obtains the compiler/components specified by Charon's
   toolchain file. Keep `charon-driver` and the required compiler libraries with
   the installation, not just a copied `charon` executable.

   `setup-charon` runs Charon's upstream test suite. For a tool-only build,
   manually clone/check out the recorded Charon revision with its submodules,
   install the matching nightly `rustfmt`, and run `make build-charon-rust`
   in that checkout instead. Aeneas's normal build compiles the vendored OCaml
   bindings. The clean VM exercised this release-build route plus the FLARE
   extraction/proof preflight; it did not run Charon's entire upstream suite.

   Check OPAM's version and initialization diagnostics. The Ubuntu 24.04 VM
   experiment upgraded the packaged OPAM 2.1.5 to the official 2.6.1 ARM64
   binary before building. OPAM's one-time format migration required retrying
   the switch command. Bubblewrap also could not configure its loopback device;
   OPAM disabled its nested build sandbox inside the isolated disposable VM.
   Retain such failures and recovery commands. Do not carry that sandbox
   workaround into an ordinary host installation or change global kernel policy.
3. Build the pinned Aeneas Lean backend with `lake build` from `backends/lean`,
   using its recorded Lean version. Inherit the user's Lake cache settings and
   follow FLARE's shared-cache guidance for genuinely missing dependencies; do
   not routinely extract Mathlib archives into every checkout. Locate the
   compiled model directory containing `Aeneas.olean` and its dependent modules,
   normally `backends/lean/.lake/build/lib/lean`. The translator binary alone is
   insufficient for checking the extracted Lean model.

   Restore the model's external imports in the provider checkout as well:

   ```sh
   python3 "$FLARE_ROOT/scripts/prepare_aeneas_lean.py" \
     --flare-root "$FLARE_ROOT" --aeneas-root /shared/pinned-aeneas
   ```

   This checks the Lean and dependency pins, then builds the named imports,
   reusing the shared Lake pool when enabled. Lean chooses the first search
   directory for an entire namespace. Adding another partial Mathlib/Batteries
   directory to `LEAN_PATH` cannot fill holes in the provider's first tree.
   The cold VM exposed missing `Mathlib.Data.List.GetD`,
   `Mathlib.Control.Monad.Cont` and `Batteries.Data.BitVec.Lemmas`; a warm host
   with more dependency artifacts already restored had hidden this setup gap.
4. Point the existing configuration interface at the completed installation:

   ```sh
   export FLARE_CHARON=/shared/pinned-aeneas/charon/bin/charon
   export FLARE_AENEAS=/shared/pinned-aeneas/bin/aeneas
   export FLARE_AENEAS_LEAN_LIB=/shared/pinned-aeneas/backends/lean/.lake/build/lib/lean
   ```

   These are example paths to replace with the resolved installation. Prefer
   environment variables or a local, ignored configuration over machine-specific
   absolute tool paths in tracked working requests. Explicit `rust_tools` request
   fields take precedence over these environment variables. Frozen certificate
   requests and identity records retain the original paths and hashes.
5. Before the application run, compile/extract a small scalar `f64` example,
   translate it, and check the resulting Lean certificate and replay with the
   selected model. Use a fresh preflight directory beneath the agreed
   verification-local cache and the normal `rust-aeneas` workflow. An internal
   generated kernel is suitable for this tool probe. This establishes tool/model
   compatibility; it does not replace extracting and proving the actual Rust
   delivery. Retain setup/preflight failures and distinguish them from rejected
   application statements or accuracy budgets.

There is no bundled one-command installer: these are agent-executed source setup
instructions. Reusing an existing installation is not a clean-machine bootstrap
test. State which route was exercised rather than claiming an untested platform
or installation procedure has passed.

## PRECiSA

The maintained `precisa` recipe targets Linux and pins PRECiSA package `4.0.4`
at `2626ba151a2915d7b148ff90ccfff5e1f764d948`, with its matching Kodiak submodule.
It was built and exercised on Ubuntu ARM64. Use Linux on other hosts; native
macOS setup is not covered by this recipe. Original-source documentation is in
the [pinned repository](https://github.com/nasa/PRECiSA/tree/2626ba151a2915d7b148ff90ccfff5e1f764d948).

Obtain missing prerequisites yourself: Git, curl, Make, G++, CMake, GMP, Boost
headers, GHC **9.6.7** and Cabal >=3.6.2.1. Linux Haskell bindists also need their
platform's runtime libraries, including libnuma and libtinfo. Keep compiler
installations in the shared versioned user cache and add their `bin` directories
to the setup command's `PATH`. Official downloads used on Ubuntu ARM64 were
[GHC 9.6.7](https://downloads.haskell.org/~ghc/9.6.7/ghc-9.6.7-aarch64-deb10-linux.tar.xz)
and [Cabal 3.12.1.0](https://downloads.haskell.org/~cabal/cabal-install-3.12.1.0/cabal-install-3.12.1.0-aarch64-linux-deb11.tar.xz).
Follow the selected bindist's installation instructions and published integrity
information; choose the matching architecture rather than copying these ARM URLs
to an x86 machine.

```sh
python3 "$FLARE_ROOT/scripts/certify_numerics.py" setup --tool precisa \
  --out /shared/tool-pool/precisa-2626ba1 --timeout 3600
export FLARE_PRECISA=/shared/tool-pool/precisa-2626ba1/install/bin/precisa
```

Setup builds the pinned Kodiak source and a hash-checked filib++ 3.0.2.2 archive
from IBEX's maintained source mirror. This avoids the unavailable historical
university download. It retains every command and a build receipt binding source
pins, compiler identity, native executable and backend library hashes. The
upstream executable has no `--version`; the provider's relocatable launcher
reports the recorded package/source identity. Use that launcher, not a bare
copied executable, for admission.

Run a small [conditional preflight](conditionals.md), inspect the actual stable
and unstable JSON results, then certify and replay. PVS files remain untrusted
evidence: a successful build or analyzer run is not a Lean proof. No PVS
installation is needed for this candidate-reconstruction route. Saved-proof
replay needs neither PRECiSA, Kodiak nor the Haskell build tools.

## Other runtimes and proof tools

For Gappa, FPTaylor and PRECiSA, the provider has pinned source-setup recipes and a shared
bounded build/logging service. Read [tool-integration.md](tool-integration.md)
for `setup --tool ... --out ...`, prerequisites and selection fields. It preserves
existing destinations and does not replace Lean or Rust-toolchain setup.

Use official downloads or user-scoped package installations for the selected
Julia, Octave, analyzer or prover version, then run a version/arithmetic preflight
and configure its existing interface. Respect user-selected runtime semantics;
Octave does not establish MATLAB runtime agreement. Report genuine licensing,
credentials, platform or permission blockers with their evidence, after attempting
the applicable supported setup. Do not substitute simulation, a different tool's
semantics or a foreign proof for the required Lean result.

## C parser and compiler

Use [pycparser](https://github.com/eliben/pycparser) **3.0** with Python 3.10+.
Reuse a matching Python installation first. Otherwise install only this parser
in the shared user cache, announcing the path. For example, on Linux:

```sh
python3 -m pip install --no-deps --target "$HOME/.cache/flare/pycparser-3.0" pycparser==3.0
```

On macOS use `$HOME/Library/Caches/flare/pycparser-3.0`. Linux also honors
`XDG_CACHE_HOME`. Set `FLARE_C_PARSER` to an explicit directory containing the
`pycparser` package when using another location. Record the selected package
version/distribution; the C evidence identifies the admitted parser profile,
not a cryptographic audit of the entire Python environment. If pip is absent,
obtain it or an isolated Python environment using the platform's supported route.
The parser is needed for C inspection, certification and frozen replay.

Obtain Clang or GCC with C11, binary64 double, 32-bit unsigned int and working
address/undefined-behavior sanitizers. Configure `source_runtime.kind` as `clang`
or `gcc` and select its executable; otherwise search PATH. Original-source
preflight tests all three compiler modes. On macOS the provider resolves the
selected Clang binary and active Xcode SDK; preserve the user's developer
selection. A missing sanitizer runtime/SDK is setup failure, not proof rejection.
Clang 21 on macOS ARM64 and GCC 13 on Ubuntu ARM64 were exercised. Compiler
versions are recorded rather than treated as interchangeable formal models.
Replay requires no C compiler or sanitizer installation.

## Optional C verification task tools

Frama-C/WP **31.0** and Why3 **1.8.2** are optional task-inspection tools;
normal C certification/replay does not require them. Read the corresponding
[Frama-C installation guide](https://frama-c.com/html/get-frama-c.html) and
[Why3 documentation](https://why3.org/doc/install.html) before source setup.
Use a versioned user-scoped OPAM switch and the releases' build prerequisites:

```sh
opam switch create /shared/tool-pool/frama-c-31.0 ocaml-system --no-switch --yes
opam install --switch=/shared/tool-pool/frama-c-31.0 frama-c.31.0 why3.1.8.2 --yes
opam exec --switch=/shared/tool-pool/frama-c-31.0 -- frama-c -version
opam exec --switch=/shared/tool-pool/frama-c-31.0 -- why3 --version
```

Replace the example path with the announced writable user-cache destination.
Choose a compatible OCaml compiler from the pinned packages' constraints instead
of changing another tool's switch. Ubuntu ARM64 setup used a system OCaml 4.13
switch and Z3 4.8.12. Obtain Z3 via its supported distribution and put it on the
export command's PATH; the exporter creates a local Why3 configuration and runs
prover detection. A bundled incompatible prover can make every task fail for a
setup reason, so inspect actual driver/prover versions and logs first.
Run `scripts/export_c_vcs.py` from the provider through `opam exec` and inspect
its `export.json`, `wp.json`, raw tasks and command logs. Solver verdicts remain
untrusted inspection evidence; this utility is not a Lean proof importer or
an implementation of the JSON numerical contract in ACSL.

## NumPy and Julia runtimes

The closed scientific profile and mixed-storage profile pin NumPy **2.4.0**,
which requires Python **3.11+**. Mixed storage additionally selects CPython
**3.13/3.14**.
Replay needs no NumPy installation; obtain it for original-source diagnostics.
Reuse a compatible environment first, otherwise announce the shared user-cache
path and install a matching distribution for this Python/platform:

```sh
python3 -m pip install --no-deps --target "$HOME/.cache/flare/numpy-2.4.0" numpy==2.4.0
```

On macOS use `$HOME/Library/Caches/flare/numpy-2.4.0`; Linux honors
`XDG_CACHE_HOME`. `FLARE_NUMPY` can locate a cached distribution when NumPy is
absent from the Python environment. An already imported incompatible NumPy
requires a fresh compatible Python environment; do not mix extension builds or
silently substitute another version. Follow NumPy's
[installation guide](https://numpy.org/install/) for a missing interpreter or
unavailable wheel, keeping setup outside the application checkout. Runtime
admission records extension/shared-library hashes and checks nearest rounding
and subnormals. Installation success is not a source correspondence proof.

Julia collection diagnostics use **1.11.7**, ordinary `Vector{Float64}` values
and `--math-mode=ieee`. Obtain the appropriate official Julia distribution in
the versioned user cache if missing; configure the existing `source_runtime`
selector with its actual executable. A local tools file can select it under
`runtimes.julia`. No Julia packages are required by the maintained vector
profile. Broader dispatch, fused broadcasting, matrix/BLAS libraries or another
runtime revision require separately reviewed semantics/admission.

Run calibration as a setup preflight, then the original application, its Lean
root and cold replay. Sampled original-source agreement, Lean validation and
physical container/compiler/library assumptions remain separate report items.
See [scientific arrays](scientific-arrays.md) for the request and retained Rust
API route. That optional delivery also needs the pinned Charon/Aeneas model.
