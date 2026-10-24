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
    parser.add_argument('--contract-cache',type=Path,help='Explicit shared cache for compiled helper contracts')
    parser.add_argument('--replay',action='store_true',help='Cold replay every checked root with producer and helper-cache reuse disabled')
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
        if 'rust_port' in request:
            for field in ('source', 'proof_source'):
                request['rust_port'][field]=str((source_request.parent/request['rust_port'][field]).resolve())
        if 'rust_application' in request:
            for field in ('files', 'lean_modules', 'components', 'licenses'):
                if field not in request['rust_application']: continue
                request['rust_application'][field] = {
                    key: str((source_request.parent/value).resolve())
                    for key, value in request['rust_application'][field].items()}
        runtime=tools.get('runtimes',{}).get(request.get('language','python'))
        if runtime and 'rust_application' not in request: request['source_runtime']=runtime
        if request.get('target')=='rust-aeneas' and tools.get('rust_tools'):
            request['rust_tools']=tools['rust_tools']
        if tools.get('analysis_tools') and 'rust_application' not in request and 'counterexample' not in request:
            request['analysis_tools'] = tools['analysis_tools']
        if args.contract_cache:
            request['contract_cache'] = str(args.contract_cache.resolve())
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
            record['metrics']={'graph_nodes':len(program.get('nodes', [])),
                'arithmetic_operations':sum(n['op']!='constant' for n in program.get('nodes', [])),
                'original_scalar_inputs':len(program.get('inputs', []))}
            if program.get('counted'):
                record['metrics'].update(source_iterations=program['counted']['iterations'],
                    expanded_operation_instances=program['counted']['iterations']*record['metrics']['arithmetic_operations'])
            if program.get('profile') == 'rust-application-proof-v1':
                record['metrics'] = {'crate_files': len(program['crate_files']),
                                     'authored_modules': len(program['lean_modules'])}
        record['stage_seconds']={p.parent.name:json.loads(p.read_text())['seconds']
                                 for p in sorted((run/'runs').glob('*/run.json'))}
        checks = [json.loads(p.read_text()) for p in (run/'runs').glob('*/run.json')]
        memory = [stage['peak_rss_bytes'] for stage in checks if stage['phase']=='check' and 'peak_rss_bytes' in stage]
        record.setdefault('metrics',{}).update({'proposal_seconds':result.get('proposal_seconds'),
                                  'lean_source_bytes':sum(p.stat().st_size for p in (run/'lean').rglob('*.lean')),
                                  'lean_source_modules':len(list((run/'lean').rglob('*.lean'))),
                                  'max_check_rss_bytes':max(memory) if memory else None})
        if (run/'proof-reuse.json').exists():
            reuse = json.loads((run/'proof-reuse.json').read_text())['modules']
            record['metrics']['reused_proof_modules'] = sum(item['reused'] for item in reuse)
        if args.replay and 'lean_root_checked' in result.get('completed_stages',[]):
            destination=out/(case['name']+'-replay')
            replay_command=[sys.executable,str(ROOT/'scripts/certify_numerics.py'),
                            'replay','--run',str(run),'--out',str(destination)]
            replay_started=time.monotonic()
            replayed=subprocess.run(replay_command,cwd=ROOT,capture_output=True,text=True,timeout=1200)
            (out/(case['name']+'.replay.stdout.txt')).write_text(replayed.stdout)
            (out/(case['name']+'.replay.stderr.txt')).write_text(replayed.stderr)
            outcome=json.loads(replayed.stdout)
            record['replay']={'status':outcome.get('status'),'seconds':time.monotonic()-replay_started,
                              'command':replay_command,'returncode':replayed.returncode}
            record['matched']=record['matched'] and replayed.returncode==0 and outcome.get('status')=='replayed'
        records.append(record)
        note=' ('+result['failure_kind']+')' if record['resource_limited'] else ''
        print(case['name']+': '+result['status']+note,flush=True)
    summary={'schema':'numerics-benchmark-run-v1','suite':args.suite,'cases':records,
             'certified_cases':[r['case'] for r in records if r['status']=='certified'],
             'counterexample_cases':[r['case'] for r in records if r['status']=='counterexample'],
             'candidate_only_cases':[r['case'] for r in records if r['status']=='candidate_only'],
             'resource_limited_cases':[r['case'] for r in records if r.get('resource_limited')],
             'passed':all(r['matched'] for r in records),'qualification':'Fresh workflow evidence; expected budget_not_met is not an observed numerical failure.'}
    save(out/'summary.json',summary)
    rows=['# Numerical '+args.suite+' suite','','Expected outcomes include explicit gaps; a matching gap is not a certificate.','',
          '| Case | Iterations | Arithmetic operations | Outcome | Run seconds | Cold replay seconds |',
          '| --- | ---: | ---: | --- | ---: | ---: |']
    rows += [f"| {r['case']} | {r.get('iterations') or '—'} | {(r.get('metrics') or {}).get('arithmetic_operations','—')} | {r['status']} | {r['seconds']:.2f} | "+
             (f"{r['replay']['seconds']:.2f}" if 'replay' in r else '—')+' |' for r in records]
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
