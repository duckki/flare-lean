# Verification provider

The `numerics` Python package orchestrates source admission, external tools,
Lean proof generation/checking, diagnostics and portable evidence. It uses the
Lean library at the repository root. The [development guide](../docs/development.md)
covers setup and validation.

## Commands

Run the stable launchers from any working directory; they locate this provider
relative to their own paths and require no package installation:

```sh
python3 /path/to/flare-lean/scripts/certify_numerics.py capabilities
python3 /path/to/flare-lean/scripts/certify_numerics.py run \
  --request /path/to/request.json --out /path/to/new-run
```

See the [workflow guide](../docs/numerical-verification.md) for complete requests,
guarantees and replay. Application artifacts use the locations agreed with the
engineer; the provider directory is maintained source, not an output location.

## Layout

| Directory | Purpose |
| --- | --- |
| `numerics/frontends` | Source parsing, admitted profiles and source/API bridges |
| `numerics/analysis` | Untrusted bounds, enclosure proposals and composition |
| `numerics/emit` | Lean/Rust generation and independent exact specifications |
| `numerics/integrations` | Tool registration, setup and Rust extraction |
| `numerics/runtimes` | Original-source execution and sampled diagnostics |
| `numerics/workflow` | Certification, frozen replay, proof reuse and delivery |
| `numerics/cli` | Command implementations behind the stable launchers |
| `manifests` | Pinned tool versions, setup recipes and Rust toolchain |
| `patches` | Hash-identified changes needed by selected external tools |
| `tests/numerics` | Provider unit tests, fresh Lean checks and rejection controls |
| `tests/tooling` | Repository tooling and process-runner regression checks |

`numerics/paths.py` owns repository resource locations. Certificate dependency
records include the provider's nested Python modules, manifests and patches.
Hashes retain file identities; the final reconstructed Lean root and axiom audit
establish the numerical result.

From the repository root:

```sh
make check
make numerics-check
```

For focused tests, use the retained file names:

```sh
python3 -m unittest discover -s provider/tests -t provider \
  -p 'test_numerics_delivery.py' -v
```
