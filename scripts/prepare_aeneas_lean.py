#!/usr/bin/env python3
"""Restore the source-built Aeneas model's external Lean imports in FLARE."""
import argparse
import json
from pathlib import Path
import re
import subprocess

from lint import mask_lean_literals


def dependency_targets(flare_root, aeneas_root):
    backend = aeneas_root / 'backends/lean'
    if (flare_root / 'lean-toolchain').read_text().strip() != (backend / 'lean-toolchain').read_text().strip():
        raise ValueError('FLARE and the Aeneas model need the same Lean toolchain')
    provider = {p['name']: p for p in json.loads((flare_root / 'lake-manifest.json').read_text())['packages']}
    model = json.loads((backend / 'lake-manifest.json').read_text())['packages']
    for package in model:
        installed = provider.get(package['name'])
        if (not installed or package.get('type') != 'git' or not package.get('rev')
                or any(package.get(k) != installed.get(k) for k in ['type', 'url', 'rev'])):
            raise ValueError('Incompatible model dependency: ' + package['name'])

    sources = [backend / 'Aeneas.lean', backend / 'AeneasMeta.lean']
    sources += sorted((backend / 'Aeneas').rglob('*.lean'))
    sources += sorted((backend / 'AeneasMeta').rglob('*.lean'))
    local = {'Aeneas', 'AeneasMeta', 'Init', 'Lean', 'Std', 'Lake'}
    targets = set()
    for source in sources:
        # The pinned source uses ordinary imports, including meta and import all.
        lines = re.findall(
            r'^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?([^\n]+)',
            mask_lean_literals(source.read_text()), re.MULTILINE,
        )
        for line in lines:
            for module in line.split():
                if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", module):
                    raise ValueError('Review unsupported model import: ' + module)
                if module.split('.')[0] not in local:
                    targets.add(module)
    if not targets or 'Mathlib' in targets:
        raise ValueError('Review the model imports before building an empty selection or all of Mathlib')
    return sorted(targets)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--flare-root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--aeneas-root', type=Path, required=True)
    args = parser.parse_args()
    try:
        targets = dependency_targets(args.flare_root.resolve(), args.aeneas_root.resolve())
    except (OSError, ValueError, KeyError) as error:
        parser.error(str(error))
    print(json.dumps({'external_model_imports': targets}, indent=2), flush=True)
    # Lean resolves a whole namespace from its first search path; appending a
    # second partial Mathlib/Batteries tree cannot fill holes in the first one.
    subprocess.run(['lake', 'build', *('+' + name for name in targets)],
                   cwd=args.flare_root, check=True)


if __name__ == '__main__':
    main()
