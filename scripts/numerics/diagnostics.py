"""Sample the actual selected source runtime, common IR and Rust build profiles."""
from fractions import Fraction as Q
import itertools
import json
import random
import struct
import sys

from .frontend import execute, word
from .runtimes import source_results


def diagnose(program, source, request, output, work, runner, runtime, with_rust=True):
    rng = random.Random(0)
    ranges = [tuple(map(Q, request['domain'][name])) for name in program.inputs]
    cases = set()
    choices = []
    for lo, hi in ranges:
        xs = [float(lo), float(hi), float((lo+hi)/2)]
        if lo <= 0 <= hi:
            tiny = float.fromhex('0x0.0000000000001p-1022')
            xs += [0.0, -0.0, tiny, -tiny]
        choices.append(list({word(x): x for x in xs if lo <= Q.from_float(x) <= hi}.values()))
    for values in itertools.islice(itertools.product(*choices), 512):
        cases.add(tuple(word(x) for x in values))
    for _ in range(128):
        values = tuple(float(lo+(hi-lo)*Q(rng.randrange(1 << 24), 1 << 24)) for lo, hi in ranges)
        if all(lo <= Q.from_float(x) <= hi for x, (lo, hi) in zip(values, ranges, strict=True)):
            cases.add(tuple(word(x) for x in values))
    rows = []
    cases = sorted(cases)
    actual_rows = source_results(program, source, cases, runtime, output, work, runner, request)
    for case, expected in zip(cases, actual_rows, strict=True):
        values = tuple(struct.unpack('>d', struct.pack('>Q', x))[0] for x in case)
        if expected != tuple(word(x) for x in execute(program, values)):
            raise ValueError('Original source runtime and extracted graph differ on a diagnostic case')
        rows.append((case, expected))
    if not rows:
        raise ValueError('No representable diagnostic inputs were found inside the requested domain')
    (output/'diagnostic-inputs.txt').write_text('\n'.join(' '.join(map(str, x[0])) for x in rows)+'\n')
    (output/'diagnostic-expected.txt').write_text('\n'.join(' '.join(map(str, x[1])) for x in rows)+'\n')
    if not with_rust:
        return {'case_count':len(rows),'source_language':program.language,
                'source_runtime':runtime['kind'],'source_IR_word_agreement':True,
                'qualification':'Sampled actual-source/IR diagnostics; the universal numerical theorem is checked separately in Lean.'}
    args = ', '.join(f'f64::from_bits(w[{i}])' for i in range(len(program.inputs)))
    returned = ['v'] if len(program.outputs) == 1 else ['v.0', 'v.1']
    body = ', '.join(x+'.to_bits()' for x in returned)
    driver = f'''use std::io::{{self, BufRead}};
#[path = {json.dumps(str(output/'rust/src/lib.rs'), ensure_ascii=False)}] mod generated;
fn main() {{
    for line in io::stdin().lock().lines() {{
        let w: Vec<u64> = line.unwrap().split_whitespace().map(|x| x.parse().unwrap()).collect();
        let v = generated::kernel({args});
        println!("{' '.join(['{}']*len(returned))}", {body});
    }}
}}
'''
    (output/'diagnostic-driver.rs.txt').write_text(driver)
    (work/'driver.rs').write_text(driver)
    for profile, flags in [('debug', []), ('release', ['-O'])]:
        binary = work/('diagnostic-'+profile)
        runner.run(profile+'-compile', ['rustc', '--edition=2021', *flags, work/'driver.rs', '-o', binary], cwd=output/'rust', phase='diagnostic')
        wrapper = work/(profile+'.py')
        wrapper.write_text('import subprocess\nfrom pathlib import Path\nsubprocess.run(['+repr(str(binary))+'], input=Path('+repr(str(output/'diagnostic-inputs.txt'))+').read_bytes(), check=True)\n')
        actual = runner.run(profile+'-execute', [sys.executable, wrapper], phase='diagnostic')
        if actual != (output/'diagnostic-expected.txt').read_text():
            raise ValueError('Source/Rust word mismatch in '+profile)
    return {'case_count': len(rows), 'source_language': program.language,
            'source_runtime': runtime['kind'],
            'source_IR_rust_debug_release_word_agreement': True,
            'qualification': 'Sampled diagnostics, separate from the universal checked Float-model theorem.'}
