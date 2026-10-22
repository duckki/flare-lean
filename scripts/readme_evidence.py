#!/usr/bin/env python3
"""Generate or replay the Lean evidence for the two README examples."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess

from numerics.counterexample import certificate_source
from numerics.workflow import ROOT, Runner, certify, dependencies, replay_run, save, sha


FILTERPY_REVISION = '3b51149ebcff0401ff1e10bf08ffca7b6bbc4a33'
FILTERPY_SOURCE_SHA256 = '4d06fb43585a20bc1155b49c0c11aac36c898102f902377f372a12aa2818cad5'
FILTERPY_LICENSE_SHA256 = '8ffce1097f1b1c0fba42e4449ef49aa05cb7b45566dd0989407839dba07af99c'
EXPECTED_BOUNDS = ['857/35184372088832', '673/17592186044416']


def files(directory):
    return {str(p.relative_to(directory)): sha(p) for p in sorted(directory.rglob('*'))
            if p.is_file() and p != directory/'manifest.json'}


def generate(filterpy, output):
    source = filterpy/'filterpy/gh/gh_filter.py'
    license_file = filterpy/'LICENSE'
    if sha(source) != FILTERPY_SOURCE_SHA256 or sha(license_file) != FILTERPY_LICENSE_SHA256:
        raise ValueError('FilterPy source/license differs from the pinned README example')
    output.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(license_file, output/'LICENSE-FilterPy')
    request = json.loads((ROOT/'benchmarks/numerics/filterpy-gh-request.json').read_text())
    request['source'] = str(source)
    save(output/'filterpy-request.json', request)
    result = certify(output/'filterpy-request.json', output/'filterpy')
    if result['status'] != 'certified':
        raise RuntimeError('FilterPy did not certify; inspect filterpy/report.md and runs/')
    if [x['bound'] for x in result['outputs']] != EXPECTED_BOUNDS:
        raise ValueError('Checked bounds changed; review the README and its request together')

    negative = output/'naive-covariance'
    negative.mkdir()
    shutil.copyfile(ROOT/'examples/numerics/naive_covariance.py', negative/'source.py')
    proof = negative/'Failure.lean'
    proof.write_text(certificate_source((negative/'source.py').read_text()))
    Runner(negative, 300).run('lean-root-check', ['lake', 'env', 'lean', proof])
    (negative/'report.md').write_text('''# Counterexample proved

- Inputs: `p = 1`, `r = 2^-54`, within the requested finite input domain.
- Binary64 posterior: `0`.
- Exact posterior: `1 / (2^54 + 1) > 0`.
- Requirement: strictly positive variance — violated.
- Lean entry: `NaiveCovarianceFailure.failure`.

This authored proof checks the admitted Python kernel and its exact reference.
The source/frontend and runtime trust boundaries still apply.
''')
    (output/'README.md').write_text('''# README example evidence

- `filterpy/report.md`: eight-update scalar error certificate and assumptions.
- `naive-covariance/report.md`: a proved violation of strict positivity.
- `manifest.json`: provider revision, source provenance and file identities.
- `LICENSE-FilterPy`: license for the frozen FilterPy source.

From a matching built FLARE checkout, replay both proofs with:

```sh
python3 scripts/readme_evidence.py replay --bundle /absolute/path/to/readme-evidence \\
  --out .cache/numerics-generated/readme-replay
```

The replay output directory must be new. Replay recompiles saved proofs and
audits their roots without running FilterPy, downloading tools or producing
new bounds. Original runtime diagnostics remain in `filterpy/`.
The optional Rust-port evidence is not included in this bundle.
''')
    provider = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    dirty = bool(subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True))
    save(output/'manifest.json', {
        'schema': 'flare-readme-evidence-v1', 'provider_revision': provider,
        'provider_dirty': dirty, 'filterpy_revision': FILTERPY_REVISION,
        'filterpy_source_sha256': FILTERPY_SOURCE_SHA256,
        'dependencies': {**dependencies(), 'scripts/readme_evidence.py': sha(__file__)},
        'files': files(output),
    })
    return {'status': 'generated', 'bundle': str(output)}


def check_bundle(bundle):
    manifest = json.loads((bundle/'manifest.json').read_text())
    if manifest.get('schema') != 'flare-readme-evidence-v1':
        raise ValueError('Expected a FLARE README evidence bundle')
    if files(bundle) != manifest['files']:
        raise ValueError('Changed or missing evidence file; download or generate a fresh bundle')
    for name, digest in manifest['dependencies'].items():
        path = (ROOT/name).resolve()
        if not path.is_relative_to(ROOT) or not path.is_file() or sha(path) != digest:
            raise ValueError('Provider dependency differs; use the recorded FLARE revision: '+name)
    if sha(bundle/'filterpy/source.py') != FILTERPY_SOURCE_SHA256:
        raise ValueError('Frozen FilterPy source differs from the README example')
    if sha(bundle/'LICENSE-FilterPy') != FILTERPY_LICENSE_SHA256:
        raise ValueError('Frozen FilterPy license differs from the pinned source license')
    request = json.loads((bundle/'filterpy/request.json').read_text())
    expected = json.loads((ROOT/'benchmarks/numerics/filterpy-gh-request.json').read_text())
    if request != expected:
        raise ValueError('FilterPy contract differs from the README example')
    result = json.loads((bundle/'filterpy/result.json').read_text())
    analysis = json.loads((bundle/'filterpy/analysis.json').read_text())
    program = json.loads((bundle/'filterpy/program.json').read_text())
    if (result['status'] != 'certified' or
            [x['bound'] for x in result['outputs']] != EXPECTED_BOUNDS or
            [analysis['accepted_bounds'][name] for name in program['outputs']] != EXPECTED_BOUNDS):
        raise ValueError('FilterPy evidence does not record the README error certificate')
    negative = bundle/'naive-covariance'
    if (negative/'source.py').read_bytes() != (ROOT/'examples/numerics/naive_covariance.py').read_bytes():
        raise ValueError('Covariance source differs from the README example')
    if (negative/'Failure.lean').read_text() != certificate_source((negative/'source.py').read_text()):
        raise ValueError('Saved refutation does not match the admitted covariance source')


def replay(bundle, output):
    if output.is_relative_to(bundle):
        raise ValueError('Replay output must be outside the frozen evidence bundle')
    check_bundle(bundle)
    output.mkdir(parents=True, exist_ok=False)
    positive = replay_run(bundle/'filterpy', output/'filterpy')
    negative = output/'naive-covariance'
    negative.mkdir()
    shutil.copyfile(bundle/'naive-covariance/Failure.lean', negative/'Failure.lean')
    Runner(negative, 300).run('lean-root-check', ['lake', 'env', 'lean', negative/'Failure.lean'])
    result = {'status': 'replayed', 'filterpy': positive,
              'counterexample_entry': 'NaiveCovarianceFailure.failure'}
    save(output/'replay.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    producer = commands.add_parser('generate')
    producer.add_argument('--filterpy', type=Path, required=True, help='Pinned FilterPy checkout')
    checker = commands.add_parser('replay')
    checker.add_argument('--bundle', type=Path, required=True)
    for command in [producer, checker]:
        command.add_argument('--out', type=Path, required=True, help='New evidence/output directory')
    args = parser.parse_args()
    if args.command == 'generate':
        result = generate(args.filterpy.resolve(), args.out.resolve())
    else:
        result = replay(args.bundle.resolve(), args.out.resolve())
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
