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

## Other runtimes and proof tools

For Gappa and FPTaylor, the provider has pinned source-setup recipes and a shared
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
