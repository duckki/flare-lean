#!/usr/bin/env python3
"""Retain Frama-C/WP and Why3 tasks for comparison; never import a foreign verdict."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil

from numerics.workflow import Runner,prepare,save,sha


VERSIONS={'frama-c':'31.0','why3':'1.8.2'}


def export(requests,output,frama_c='frama-c',why3='why3',timeout=120):
    selected=[prepare(path) for path in requests]
    if any(p.language!='c' or questions for _,_,p,questions in selected):
        raise ValueError('Provide complete admitted C requests')
    sources=[source.read_bytes() for _,source,_,_ in selected]
    if any(source!=sources[0] for source in sources):
        raise ValueError('Export one C translation unit at a time')
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    source=output/'source.c';source.write_bytes(sources[0])
    runner=Runner(output,timeout)
    record={'schema':'c-foreign-vc-export-v1','status':'unresolved',
        'source_sha256':sha(source),'functions':[p.function for _,_,p,_ in selected],
        'lean_proof_imported':False,'qualification':
        'Task inspection only. WP reads source ACSL; the retained JSON numerical requests are not translated into ACSL. Solver verdicts are not FLARE certificates or comparisons of the same numerical proof target.'}
    try:
        tools={}
        for name,value in [('frama-c',frama_c),('why3',why3)]:
            path=shutil.which(value)
            if not path:raise RuntimeError('Missing task-export tool '+name)
            path=str(Path(path).resolve())
            version=runner.run(name+'-version',[path,'-version' if name=='frama-c' else '--version'],phase='admission')
            if not re.search(r'(?<![\d.])'+re.escape(VERSIONS[name])+r'(?![\d.])',version):
                raise RuntimeError('Unsupported '+name+' task interface; expected '+VERSIONS[name])
            tools[name]={'path':path,'sha256':sha(path),'version':version.strip()}
        record['tools']=tools
        config=output/'why3.conf'
        environment={'WHY3CONFIG':str(config),'PATH':str(Path(tools['why3']['path']).parent)+os.pathsep+os.environ['PATH']}
        runner.run('why3-detect',[tools['why3']['path'],'config','detect'],env=environment,phase='admission')
        runner.run('why3-provers',[tools['why3']['path'],'config','list-provers'],env=environment,phase='admission')
        report=output/'wp.json'
        command=[tools['frama-c']['path'],'-wp','-wp-rte','-wp-model','Typed+float',
                 '-wp-prover','z3','-wp-timeout','1','-wp-debug','1',
                 '-wp-fct',','.join(record['functions']),'-wp-print','-wp-out',output/'tasks',
                 '-wp-report-json',report,source]
        runner.run('wp-why3-export',command,cwd=output,env=environment,phase='analysis')
        goals=json.loads(report.read_text())
        tasks=[p for p in (output/'tasks').rglob('*') if p.is_file()]
        if not isinstance(goals,list) or not goals or not tasks:
            raise RuntimeError('WP/Why3 did not retain goals and task files; inspect tool/prover setup logs')
        record.update(status='task_evidence_only',goals=goals,
            task_files={str(p.relative_to(output)):sha(p) for p in sorted(tasks)})
        for i,(request,_,program,_) in enumerate(selected):
            save(output/('request-'+str(i)+'.json'),{**request,'source':'source.c'})
        record['provider_sha256']=sha(Path(__file__))
    except (RuntimeError,ValueError,OSError) as error:
        record.update(error=str(error),failure_stage=getattr(runner,'last_stage','tool-admission'))
        raise
    finally:save(output/'export.json',record)
    return record


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--request',required=True,action='append',type=Path)
    parser.add_argument('--out',required=True,type=Path)
    parser.add_argument('--frama-c',default='frama-c')
    parser.add_argument('--why3',default='why3')
    args=parser.parse_args()
    try:r=export(args.request,args.out,args.frama_c,args.why3)
    except (ValueError,RuntimeError,OSError) as error:
        print(json.dumps({'status':'unresolved','error':str(error)}));return 2
    print(json.dumps({k:v for k,v in r.items() if k not in ('goals','task_files')},indent=2));return 0


if __name__=='__main__':raise SystemExit(main())
