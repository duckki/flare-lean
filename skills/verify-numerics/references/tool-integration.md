# Run registered numerical producers

Read the provider's `capabilities` output for adapter roles, supported versions,
arithmetic constraints and setup recipes. The current external producers are
`gappa`, `fptaylor` and `precisa`; `lean-flare` remains the default producer and
independent checking path. `rust-aeneas` supplies extraction when requested.

Add `"producer": "gappa"`, `"producer": "fptaylor"` or `"producer": "precisa"`
to an otherwise complete request. Configure `analysis_tools` as a map from tool name to `executable`,
optional expected `sha256`, and optional tool-data `base` directory. Environment
variables `FLARE_GAPPA` / `FLARE_FPTAYLOR` / `FLARE_PRECISA` and `PATH` are
fallbacks. Preserve source, domain, independent specification, units and requirements.

The external routes save proof-bearing or candidate output, then reconstruct the
**candidate conclusion** in Lean: the Gappa query's exact dyadic radius or the
actual FPTaylor hexadecimal bound, or PRECiSA's maximum stable/unstable bound.
They cannot substitute a looser budget. Failed Lean arguments remain unresolved. Gappa's Coq
trace is retained rather than imported; this is not a general foreign-proof importer.

The scalar validator uses nearest-rounding theorems, checked polynomial rewrites,
interval inference and bounded domain subdivision. It admits at most 32 IR nodes,
256 polynomial terms, degree 16 and 16 input boxes, with arithmetic magnitude at most
`2^1000` and positive native/exact divisor floors. The default producer also tries
it when compositional analysis loses a floor or misses a budget. Preserve the
original contract when search or proof checking fails. Review per-box domains,
rounding allowances and conclusions in `analysis.json`; saved proofs establish
that all cases cover the original domain.

For terminal scalar Python conditionals, read [conditionals.md](conditionals.md).
PRECiSA's candidate is checked across all four native/exact flows, even if the
analyzer claims stability. PVS files are retained rather than imported. This
profile currently uses Lean delivery; both arms must satisfy arithmetic premises
on the full domain. The default branch producer attempts the requested allowance.

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
Lean/Rust setup in [tool-setup.md](tool-setup.md). The same guide covers the
Linux PRECiSA recipe, GHC/Cabal prerequisites and versioned launcher.

Run normal `plan`, `run`, `audit` and `replay` commands. Review `obligation.json`,
`evidence.json`, raw queries/output and `analysis.json` alongside the root proof.
Missing tools, unsupported versions and changed tool hashes have separate failure
kinds. Saved-proof replay uses neither setup nor producers.

For provider extensions, prefer another adapter, a reusable evidence checker or
verified inference over per-application numerical proof patches. An adapter can
emit a Lean proof module through the same typed root check. The
[provider integration guide](https://github.com/duckki/flare-lean/blob/main/docs/tool-integration.md)
defines these interfaces and their tests.
