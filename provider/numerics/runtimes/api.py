"""Word-level runtime diagnostics for the admitted ordinary scalar API.

These sampled checks supplement the Lean correspondence theorem. The driver is
kept separate from the reusable crate; replay never executes either runtime.
"""
import ast
import json
import os
from pathlib import Path
import random
import shutil
import struct
import sys


def bits(value):
    return struct.unpack('>Q', struct.pack('>d', float(value)))[0]


def cases(description):
    rng = random.Random(7357)
    result = []
    for i in range(128):
        args = {name: rng.uniform(-2, 2) for name in description['parameters']}
        # Exercise both signs, exact powers of two and different stored gains.
        if 'dt' in args:
            args['dt'] = (0.125, -0.5, 2.0)[i % 3]
        updates = []
        for j in range(8):
            z = (-0.0, 0.0, 5e-324, -5e-324)[j] if i == 0 and j < 4 else rng.uniform(-10, 10)
            options = {name: None if (i+j+k) % 3 == 0 else rng.uniform(-1, 1)
                       for k, name in enumerate(description['options'])}
            updates.append({'z': z, 'options': options})
        result.append({'arguments': args, 'updates': updates})
    return result


def python_words(source, function, inputs, fields):
    """Execute only the exact selected original bodies, with real NumPy scalars."""
    import numpy as np
    name, method = function.split('.')
    tree = ast.parse(Path(source).read_text())
    original = next(n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == name)
    selected = [n for n in original.body if isinstance(n, ast.FunctionDef) and n.name in ('__init__', method)]
    cls = ast.ClassDef(name=name, bases=[], keywords=[], body=selected, decorator_list=[])
    namespace = {}
    for n in tree.body:
        if isinstance(n, ast.Import):
            for alias in n.names:
                if alias.name == 'numpy':
                    namespace[alias.asname or alias.name] = np
    exec(compile(ast.fix_missing_locations(ast.Module(body=[cls], type_ignores=[])), str(source), 'exec'), namespace)
    words = []
    for case in inputs:
        state = namespace[name](**case['arguments'])
        words.append([bits(getattr(state, f)) for f in fields])
        for update in case['updates']:
            getattr(state, method)(update['z'], **update['options'])
            words.append([bits(getattr(state, f)) for f in fields])
    return {'numpy_version': np.__version__, 'words': words}


def rust_driver(description, inputs, rust_type):
    def literal(value):
        return 'f64::from_bits('+str(bits(value))+'u64)'
    def snapshot():
        return 'println!("{}", ['+', '.join('s.'+f+'.to_bits().to_string()' for f in description['fields'])+'].join(","));'
    lines = ['use numerics_kernel::'+rust_type.replace('Workflow.Generated.', '').replace('.', '::')+';',
             'fn main() {', 'let cases = [']
    typ = rust_type.split('.')[-1]
    for case in inputs:
        args = ', '.join(literal(case['arguments'][p]) for p in description['parameters'])
        updates = []
        for update in case['updates']:
            values = [literal(update['z'])]+['None' if v is None else 'Some('+literal(v)+')' for v in update['options'].values()]
            updates.append('('+', '.join(values)+')')
        lines.append('(['+args+'], ['+', '.join(updates)+']),')
    names = list(description['options'])
    lines += ['];', 'for (a, updates) in cases {',
        'let mut s = '+typ+'::new('+', '.join('a['+str(i)+']' for i in range(len(description['parameters'])))+');',
        snapshot(), 'for (z, '+', '.join(names)+') in updates {',
        's.'+description['method']+'(z, '+', '.join(names)+');', snapshot(), '}', '}', '}']
    return '\n'.join(lines)+'\n'


def run(output, request, runner, work):
    from numerics.workflow.certification import ROOT, save, sha
    api = request['rust_application'].get('source_api')
    if api is None or 'runtime' not in api:
        return None
    from numerics.integrations.registry import ToolError
    runtime = Path(shutil.which(api['runtime']) or api['runtime']).expanduser().resolve()
    if not runtime.is_file() or not os.access(runtime, os.X_OK):
        raise ToolError('missing_tool', 'Missing scalar API Python executable: '+str(runtime))
    try:
        runner.run('python-api-setup', [runtime, '-c', 'import numpy; print(numpy.__version__)'],
                   phase='admission')
    except RuntimeError as error:
        raise ToolError('tool_setup_failed', 'Scalar API diagnostics need a working Python/NumPy installation; see python-api-setup logs') from error
    description = json.loads((output/'source-api.json').read_text())
    component = output/'components'/api['component']
    selected = json.loads((component/'request.json').read_text())
    inputs = cases(description)
    save(output/'api-inputs.json', inputs)
    driver = output/'drivers/api'
    (driver/'src').mkdir(parents=True)
    (driver/'Cargo.toml').write_text('[package]\nname="api-driver"\nversion="0.1.0"\nedition="2021"\n'
        '[dependencies]\nnumerics-kernel={path="../../rust"}\n[workspace]\n')
    (driver/'rust-toolchain.toml').write_bytes((output/'rust/rust-toolchain.toml').read_bytes())
    (driver/'src/main.rs').write_text(rust_driver(description, inputs, api['rust_type']))
    runtime = str(runtime)
    expected = json.loads(runner.run('python-api', [runtime, ROOT/'scripts/api_diagnostics.py',
        component/selected['source'], selected['function'], output/'api-inputs.json', output/'source-api.json'],
        phase='diagnostic'))
    for mode in ('debug', 'release'):
        text = runner.run('api-'+mode, ['cargo', 'run', '--quiet', *(['--release'] if mode == 'release' else [])],
            cwd=driver, env={'CARGO_TARGET_DIR': str(work/'api')}, phase='diagnostic')
        actual = [[int(x) for x in line.split(',')] for line in text.splitlines()]
        if actual != expected['words']:
            raise ValueError('Python/Rust complete API state word mismatch: '+mode)
    record = {'schema': 'numerics-api-diagnostics-v1', 'runtime': runtime, 'runtime_sha256': sha(runtime),
        'numpy_version': expected['numpy_version'], 'cases': len(inputs), 'updates': 8*len(inputs),
        'snapshots': len(expected['words']), 'fields': description['fields'], 'modes': ['debug', 'release'],
        'qualification': 'Sampled original-body runtime diagnostics, not the Lean proof or whole Python module execution.'}
    save(output/'api-diagnostics.json', record)
    return record


if __name__ == '__main__':
    print(json.dumps(python_words(sys.argv[1], sys.argv[2], json.loads(Path(sys.argv[3]).read_text()),
        json.loads(Path(sys.argv[4]).read_text())['fields'])))
