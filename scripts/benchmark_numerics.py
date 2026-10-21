#!/usr/bin/env python3
"""Run fresh maintained numerical workflows; report optional tools separately."""
import argparse
import json
import shutil
from pathlib import Path
import subprocess
import sys
import time
from numerics.workflow import ROOT,save


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',required=True,type=Path)
    parser.add_argument('--suite',choices=['smoke','scale'],default='smoke')
    parser.add_argument('--case',action='append',default=[])
    parser.add_argument('--include-optional',action='store_true')
    parser.add_argument('--tools',type=Path,help='Local rust_tools and language runtimes overrides')
    args=parser.parse_args(); out=args.out.resolve();out.mkdir(parents=True,exist_ok=False)
    manifest=ROOT/'benchmarks/numerics'/('scenarios.json' if args.suite=='smoke' else 'scale.json')
    suite=json.loads(manifest.read_text());tools=json.loads(args.tools.read_text()) if args.tools else {}
    records=[]
    known={c['name'] for c in suite['cases']}
    if set(args.case)-known: parser.error('Unknown case: '+', '.join(set(args.case)-known))
    for case in suite['cases']:
        if args.case and case['name'] not in args.case: continue
        if case['optional'] and not args.include_optional and not args.case: continue
        if case.get('kind')=='graph_probe':
            from numerics.workflow import Runner
            run=out/case['name'];run.mkdir()
            graph=(manifest.parent/case['graph']).resolve()
            frozen=run/'graph.json.gz';shutil.copyfile(graph,frozen)
            command=[sys.executable,'-m','numerics.scale','--graph',str(frozen),'--outputs',*case['outputs']]
            started=time.monotonic()
            try:
                text=Runner(run,120).run('analysis',command,env={'PYTHONPATH':str(ROOT/'scripts')},phase='analysis')
                result=json.loads(text)
            except RuntimeError as error:
                result={'status':'unresolved','error':str(error),'failure_stage':'analysis_command'}
            save(run/'probe.json',result)
            record={'case':case['name'],'kind':'graph_probe','expected':case['expected'],
                    'optional':case['optional'],'family':case['family'],'iterations':case['iterations'],
                    'status':result['status'],'failure_stage':result.get('failure_stage'),
                    'error':result.get('error'),'metrics':result.get('metrics'),
                    'outputs':result.get('outputs',[]),'failure_origin':result.get('failure_origin'),
                    'entry_theorem':None,'seconds':time.monotonic()-started,'command':command,
                    'qualification':'Analysis probe only; never a certification result.'}
            record['matched']=matches(case,result)
            records.append(record)
            print(case['name']+': '+record['status']+' (model analysis only)',flush=True)
            continue
        source_request=(manifest.parent/case['request']).resolve()
        request=json.loads(source_request.read_text())
        request['source']=str((source_request.parent/request['source']).resolve())
        runtime=tools.get('runtimes',{}).get(request.get('language','python'))
        if runtime: request['source_runtime']=runtime
        if request.get('target')=='rust-aeneas' and tools.get('rust_tools'):
            request['rust_tools']=tools['rust_tools']
        selected=out/(case['name']+'.json');save(selected,request)
        start=time.monotonic();run=out/case['name']
        command=[sys.executable,str(ROOT/'scripts/certify_numerics.py'),'run','--request',str(selected),'--out',str(run)]
        completed=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,timeout=1200)
        (out/(case['name']+'.stdout.txt')).write_text(completed.stdout)
        (out/(case['name']+'.stderr.txt')).write_text(completed.stderr)
        result=json.loads((run/'result.json').read_text()) if (run/'result.json').exists() else json.loads(completed.stdout)
        record={'case':case['name'],'status':result['status'],'expected':case['expected'],
                'kind':'workflow','family':case.get('family'),'iterations':case.get('iterations'),
                'optional':case['optional'],'failure_stage':result.get('failure_stage'),
                'matched':matches(case,result),'seconds':time.monotonic()-start,
                'entry_theorem':result.get('entry_theorem'),'error':result.get('error'),
                'failure_kind':result.get('failure_kind'),
                'resource_limited':result.get('failure_kind') in ['timeout','heartbeats'],
                'outputs':result.get('outputs',[]),'command':command}
        if (run/'program.json').is_file():
            program=json.loads((run/'program.json').read_text())
            record['metrics']={'graph_nodes':len(program['nodes']),
                'arithmetic_operations':sum(n['op']!='constant' for n in program['nodes']),
                'original_scalar_inputs':len(program['inputs'])}
        record['stage_seconds']={p.parent.name:json.loads(p.read_text())['seconds']
                                 for p in sorted((run/'runs').glob('*/run.json'))}
        records.append(record)
        note=' ('+result['failure_kind']+')' if record['resource_limited'] else ''
        print(case['name']+': '+result['status']+note,flush=True)
    summary={'schema':'numerics-benchmark-run-v1','suite':args.suite,'cases':records,
             'certified_cases':[r['case'] for r in records if r['status']=='certified'],
             'candidate_only_cases':[r['case'] for r in records if r['status']=='candidate_only'],
             'resource_limited_cases':[r['case'] for r in records if r.get('resource_limited')],
             'passed':all(r['matched'] for r in records),'qualification':'Fresh workflow evidence; expected budget_not_met is not an observed numerical failure.'}
    save(out/'summary.json',summary)
    rows=['# Numerical '+args.suite+' suite','','Expected outcomes include explicit gaps; a matching gap is not a certificate.','',
          '| Case | Iterations | Arithmetic operations | Outcome | Seconds |',
          '| --- | ---: | ---: | --- | ---: |']
    rows += [f"| {r['case']} | {r.get('iterations') or '—'} | {(r.get('metrics') or {}).get('arithmetic_operations','—')} | {r['status']} | {r['seconds']:.2f} |" for r in records]
    (out/'summary.md').write_text('\n'.join(rows)+'\n')
    return 0 if summary['passed'] else 1


def matches(case,result):
    if (case.get('resource_limits_allowed') and result['status']=='unresolved'
            and result.get('failure_stage')=='lean-proof'
            and result.get('failure_kind') in ['timeout','heartbeats']):
        return True
    return (result['status']==case['expected']
            and (not case.get('expected_failure_stage') or result.get('failure_stage')==case['expected_failure_stage'])
            and case.get('expected_error_contains','') in result.get('error',''))


if __name__=='__main__': raise SystemExit(main())
