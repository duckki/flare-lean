#!/usr/bin/env python3
"""Exercise held-out applications, portable roots and producer-free replay.

Run inside each recorded platform after setup. A successful agent-operated run
is automated reproduction, never independent engineer reproduction.
"""
import argparse
import json
import platform
import sys
import time
from pathlib import Path
from unittest.mock import patch

from numerics.workflow.certification import ROOT, certify, replay_run, save
from numerics.workflow.delivery import pack, unpack, recheck


def run(output,tools=None):
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    record={'schema':'numerics-release-v1','platform':{'system':platform.system(),'machine':platform.machine(),
        'python':sys.version},'cases':{},'qualification':'Agent-operated automated reproduction. VM/emulation/base-OS provisioning must be recorded separately; independent engineer reproduction is pending.'}
    cases={p.name:p/'request.json' for p in (ROOT/'benchmarks/numerics/heldout').iterdir() if p.is_dir()}
    cases['covariance-counterexample']=ROOT/'examples/numerics/counterexamples/naive_covariance.json'
    cases['ros-positivity-counterexample']=ROOT/'benchmarks/numerics/heldout/ros-angles/positivity_witness.json'
    if tools and tools.get('rust_tools'):
        selected=json.loads((ROOT/'examples/numerics/scientific/calibration_python_rust.json').read_text())
        base=ROOT/'examples/numerics/scientific'
        selected['source']=str(base/selected['source'])
        selected['rust_port']={**selected['rust_port'],**{k:str(base/selected['rust_port'][k]) for k in ('source','proof_source')}}
        selected['rust_tools']=tools['rust_tools']
        save(output/'rust-request.json',selected)
        cases['retained-array-rust']=output/'rust-request.json'
    try:
        for name,request in cases.items():
            run_dir=output/name;result=certify(request,run_dir)
            if result['status'] not in ('certified','counterexample'):raise RuntimeError(name+': '+result.get('error',result['status']))
            archive=output/(name+'.tar.gz');packed=pack(run_dir,archive)
            moved=output/(name+'-portable');unpack(archive,moved)
            with patch('numerics.runtimes.source.admit_runtime',side_effect=AssertionError('Source runtime invoked during replay')), \
                 patch('numerics.integrations.registry.Session.execute',side_effect=AssertionError('Producer invoked during replay')), \
                 patch('numerics.integrations.rust.extract',side_effect=AssertionError('Translator invoked during replay')), \
                 patch('numerics.runtimes.source.source_results',side_effect=AssertionError('Source executed during replay')), \
                 patch('numerics.runtimes.scientific.numpy',side_effect=AssertionError('NumPy invoked during replay')):
                started=time.monotonic();replay=replay_run(moved,output/(name+'-replay'));replay_seconds=time.monotonic()-started
                started=time.monotonic();checked=recheck(moved,request,output/(name+'-recheck'));recheck_seconds=time.monotonic()-started
            runs=[json.loads(p.read_text()) for p in (run_dir/'runs').glob('*/run.json')]
            record['cases'][name]={'status':result['status'],'entry_theorem':result['entry_theorem'],
                'generation_seconds':result['elapsed_seconds'],'stage_seconds':{p.parent.name:json.loads(p.read_text())['seconds'] for p in (run_dir/'runs').glob('*/run.json')},
                'peak_completed_child_rss_bytes':max((r.get('peak_rss_bytes') or 0 for r in runs),default=0),
                'bundle_bytes':archive.stat().st_size,'bundle_sha256':packed['sha256'],
                'replay':replay['status'],'recheck':checked['status'],
                'replay_seconds':replay_seconds,'recheck_seconds':recheck_seconds}
            print(json.dumps({'case':name,**record['cases'][name]}),flush=True)
        record['status']='passed'
    except (ValueError,RuntimeError,OSError) as error:
        record.update(status='failed',error=str(error));raise
    finally:save(output/'release.json',record)
    return record


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--out',required=True,type=Path)
    parser.add_argument('--tools',type=Path,help='Optional existing rust_tools selection; also checks retained Rust delivery')
    args=parser.parse_args();run(args.out,json.loads(args.tools.read_text()) if args.tools else None)
