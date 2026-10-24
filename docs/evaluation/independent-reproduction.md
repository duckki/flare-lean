# Independent delivery reproduction

This is a follow-up to the completed automated delivery milestone.

Reproduce one positive certificate and one counterexample from a delivered
handoff, using this page without the original agent conversation. Record the
engineer's result separately from automated regression results. An agent can
help execute the commands; a human engineer must review the reports, observe
the results and record any help needed.

## Handoff contents

The maintainer supplies:

- `provider.tar.gz`: the complete FLARE source at the recorded Git revision.
- `positive.tar.gz`: the Chemicals `API_to_SG` certificate and frozen sources.
- `counterexample.tar.gz`: the covariance strict-positivity failure and witness.
- `positive-report.md` and `counterexample-report.md`: the original reports.
- `manifest.json`: provider revision, toolchain, file hashes and expected roots.
- `README.md`: these instructions, and `RESULTS.md`: the engineer's results form.

The positive result bounds specific-gravity error by `1/35184372088832`, within
the requested `1/1000000000000`, for finite binary64 API inputs in `[10, 80]`.
The counterexample uses `p = 1` and `r = 2^-54`: the source returns zero while
the independent exact variance is `1/18014398509481985`, which is positive.
Read both reports for the frontend, arithmetic and application trust boundaries.

## 1. Choose locations and check the delivery

Use a Linux or macOS machine with Python 3.10 or newer, curl, Git, Make and a
working C/C++ build environment. Linux needs the compiler/linker prerequisites for Lean;
macOS needs the Command Line Tools. Network access is needed for initial Lean
and Mathlib setup. Neither case needs NumPy, CBMC, Gappa or Rust tools.

Choose an existing unpacked handoff directory, a new workspace and a new tool
pool outside that workspace. Replace the example paths before running commands:

```sh
export HANDOFF="/absolute/path/to/milestone14-handoff"
export WORK="/absolute/path/to/new-reproduction"
export TOOLS="/absolute/path/to/new-flare-tool-pool"
```

Check that the supplied files match the manifest:

```sh
python3 - <<'PY'
import hashlib, json, os
from pathlib import Path
root = Path(os.environ['HANDOFF'])
manifest = json.loads((root / 'manifest.json').read_text())
for name, expected in manifest['files'].items():
    actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit('Hash mismatch: ' + name)
print('File hashes match; provider revision:', manifest['provider_revision'])
PY
```

Hashes detect changed files; they do not authenticate the sender or prove a
theorem. Obtain the handoff through the agreed delivery channel.

## 2. Set up the supplied provider

```sh
mkdir "$WORK"
tar -xzf "$HANDOFF/provider.tar.gz" -C "$WORK"
export PROVIDER="$WORK/flare-lean"
python3 "$PROVIDER/scripts/bootstrap_numerics.py" \
  --provider "$PROVIDER" --tools "$TOOLS" --out "$WORK/setup"
export ELAN_HOME="$TOOLS/elan"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2
```

Bootstrap installs the pinned Lean release, obtains the needed Mathlib build
artifacts and builds FLARE. It writes setup receipts under `$WORK/setup` and
does not edit shell profiles. Shared Lake caching is optional; pass
`--shared-cache` to bootstrap if desired. Preserve setup failures and logs.

## 3. Replay both delivered roots

```sh
python3 "$PROVIDER/scripts/certify_numerics.py" unpack \
  --archive "$HANDOFF/positive.tar.gz" --out "$WORK/positive"
python3 "$PROVIDER/scripts/certify_numerics.py" replay \
  --run "$WORK/positive" --out "$WORK/positive-replay" --timeout 240
python3 "$PROVIDER/scripts/certify_numerics.py" unpack \
  --archive "$HANDOFF/counterexample.tar.gz" --out "$WORK/counterexample"
python3 "$PROVIDER/scripts/certify_numerics.py" replay \
  --run "$WORK/counterexample" --out "$WORK/counterexample-replay" --timeout 240
```

Each replay freshly compiles the frozen Lean proof and checks the independently
reconstructed root type and transitive axiom closure. It uses no analyzer,
translator, original source execution or LLM. Unpacking alone is an integrity
check. The original reports retain the sender's paths as provenance; use the
paths above to replay at the new location.

Expected results in the two `replay.json` files:

| Run | `status` | `certificate_status` | `entry_theorem` |
| --- | --- | --- | --- |
| Positive | `replayed` | `certified` | `Workflow.Certificate.certificate` |
| Counterexample | `replayed` | `counterexample` | `Workflow.Counterexample.counterexample` |

## 4. Record the engineer's result

Complete the supplied `RESULTS.md` with your name or identifier, date, platform,
provider revision, observed results, report review and any needed assistance.
Return it together with `setup/bootstrap.json`, the two `replay.json` files and
their `runs/` logs. Keep failed attempts too; use new output directories for
retries. A timeout or setup failure is not a numerical counterexample.

The maintainer checks the returned evidence and records the result in the
delivery evaluation. An unfilled template, copied expected output or an
agent-only rehearsal does not establish independent engineer reproduction.
