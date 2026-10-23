# Run registered numerical producers

Read the provider's `capabilities` output for adapter roles, supported versions,
arithmetic constraints and setup recipes. The current external producers are
`gappa` and `fptaylor`; `lean-flare` remains the default producer and independent
checking path. `rust-aeneas` supplies extraction when requested.

Add `"producer": "gappa"` or `"producer": "fptaylor"` to an otherwise complete
request. Configure `analysis_tools` as a map from tool name to `executable`,
optional expected `sha256`, and optional tool-data `base` directory. Environment
variables `FLARE_GAPPA` / `FLARE_FPTAYLOR` and `PATH` are fallbacks. Preserve the
source, domain, independent specification, units and engineering requirements.

The initial external routes save proof-bearing or candidate output, then
independently prove the **requested budgets** in Lean. Gappa Coq traces and sharper
FPTaylor candidates remain untrusted raw evidence. If independent checking cannot
prove the requested bound, report the remaining obligation. Do not describe this
route as a general foreign-proof importer or mark printed tighter bounds checked.

Reuse compatible tools. Otherwise obtain missing prerequisites and use the
shared source-setup service in the agreed versioned user cache:

```sh
python3 "$FLARE_ROOT/scripts/certify_numerics.py" setup --tool gappa \
  --out /shared/tool-pool/gappa-1.8.3
python3 "$FLARE_ROOT/scripts/certify_numerics.py" setup --tool fptaylor \
  --out /shared/tool-pool/fptaylor-b5a77cae
```

Gappa needs C++, Flex/Bison, Boost headers and GMP/MPFR development files; the
release uses bundled `remake`. The portable FPTaylor build
needs OCaml 4, Num, Make and C; use an isolated compiler/switch as necessary.
`--make-arg 'NAME=value'` passes a build override. Keep setup logs, source identities
and failures. Existing destinations are preserved. Tool setup is separate from
Lean/Rust setup in [tool-setup.md](tool-setup.md).

Run normal `plan`, `run`, `audit` and `replay` commands. Review `obligation.json`,
`evidence.json`, raw queries/output and `analysis.json` alongside the root proof.
Missing tools, unsupported versions and changed tool hashes have separate failure
kinds. Saved-proof replay uses neither setup nor producers.

For provider extensions, prefer another adapter, a reusable evidence checker or
verified inference over per-application numerical proof patches. An adapter can
emit a Lean proof module through the same typed root check. The
[provider integration guide](https://github.com/duckki/flare-lean/blob/main/docs/tool-integration.md)
defines these interfaces and their tests.
