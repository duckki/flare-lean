#!/usr/bin/env python3
"""Reproduce bounded integration trials; these adapters are evaluation-only."""
import argparse
import csv
import hashlib
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import time
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'provider'))
from numerics.analysis import checked_bounds, scalar
from numerics.frontends.scalar import number
from numerics.integrations import registry
from numerics.integrations.registry import Adapter
from numerics.integrations.adapter_external import applicable, node_expression
from numerics.workflow.certification import Runner, certify, prepare, replay_run, save
from fractions import Fraction as Q

PINS=json.loads((ROOT/'provider/manifests/evaluation-tools.json').read_text())['tools']
FIXTURES=Path(__file__).parent


def source_pin(path,name):
    actual=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
    if actual!=PINS[name]['revision']:raise ValueError('Wrong '+name+' source revision')
    changed=set(subprocess.check_output(['git','-C',str(path),'diff','--name-only','-z','HEAD']).decode().split('\0'))-{''}
    allowed={'src/main/scala/daisy/backend/InfoPhase.scala'} if name=='daisy' else set()
    if changed!=allowed:raise ValueError('Unexpected tracked changes in '+name+' source')
    return actual


def metrics(run):
    records=[json.loads(p.read_text()) for p in sorted((run/'runs').glob('*/run.json'))]
    return {'check_seconds':sum(r['seconds'] for r in records if r['phase']=='check'),
            'analysis_seconds':sum(r['seconds'] for r in records if r['phase']=='analysis'),
            'peak_child_rss_bytes':max((r.get('peak_rss_bytes',0) or 0 for r in records),default=0),
            'lean_source_bytes':sum(p.stat().st_size for p in (run/'lean').rglob('*.lean'))}


def checked_run(request,out):
    started=time.monotonic();result=certify(request,out)
    record={'status':result['status'],'seconds':time.monotonic()-started,
            'error':result.get('error'),'failure_stage':result.get('failure_stage'),
            'proposal_seconds':result.get('proposal_seconds'),
            'outputs':result.get('outputs'),**metrics(out)}
    evidence=out/'evidence.json'
    if evidence.exists():
        record['raw_candidates']=[item['details']['raw_candidate_bounds'] for item in json.loads(evidence.read_text())['records'] if 'raw_candidate_bounds' in item.get('details',{})]
    record['compiled_module_bytes']=sum(path.stat().st_size for path in (out/'.work/build').rglob('*.olean*'))
    if result['status']=='certified':
        with patch.object(registry.Session,'execute',side_effect=AssertionError('producer called')), \
             patch.object(registry.Session,'tool',side_effect=AssertionError('tool called')), \
             patch.object(checked_bounds,'infer',side_effect=AssertionError('inference called')):
            started=time.monotonic();replay=replay_run(out,out.parent/(out.name+'-replay'))
        record.update(replay=replay['status'],replay_seconds=time.monotonic()-started)
    return record


def typed(out):
    records=[]
    for name in ['power32','power256','zero_product','zero_energy']:
        request,source,_,_=prepare(ROOT/'examples/numerics/typed-evidence'/(name+'.json'))
        case=out/name;case.mkdir()
        save(case/'request.json',{**request,'source':str(source)})
        with patch.object(checked_bounds,'supported',return_value=False):
            before=checked_run(case/'request.json',case/'before')
        after=checked_run(case/'request.json',case/'after')
        records.append({'case':name,'before':before,'after':after})
        save(out/'results.json',records)
    # Hold source, domain, specification, budget AND candidate fixed for the
    # backend cost comparison. Neither trial invokes a foreign producer.
    request,source,_,_=prepare(ROOT/'examples/numerics/enclosures/quartic_gappa.json')
    request={**request,'source':str(source),'producer':'annotation-trial'}
    candidate=str(Q(request['outputs'][0]['limit']))
    adapter=Adapter('annotation-trial','producer','fixed-numeric-candidate','Fixed-candidate comparison',None)
    for backend in ['scalar','typed']:
        def produce(session):
            proposal=(scalar.proposal if backend=='scalar' else checked_bounds.proposal)(
                session.program,session.request,[candidate],{'evaluation':'fixed-candidate'})
            return proposal,proposal.details
        from dataclasses import replace
        selected=registry.adapters();selected[adapter.name]=replace(adapter,execute=produce)
        path=out/(backend+'-request.json');save(path,request)
        with patch.object(registry,'adapters',return_value=selected):
            record=checked_run(path,out/(backend+'-fixed'))
        records.append({'case':'quartic-fixed-candidate','backend':backend,'candidate':candidate,**record})
        save(out/'results.json',records)


def leancert(source,out):
    source_pin(source,'leancert')
    a=json.loads((source/'lake-manifest.json').read_text())['packages']
    b=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
    if any(next(p['rev'] for p in b if p['name']==x['name'])!=x['rev'] for x in a):
        raise ValueError('LeanCert and FLARE dependency revisions differ')
    core=out/'core';shutil.copytree(source,core,ignore=shutil.ignore_patterns('.git','.lake'))
    (core/'.lake').mkdir();(core/'.lake/packages').symlink_to(ROOT/'.lake/packages',target_is_directory=True)
    runner=Runner(out,timeout=600)
    runner.run('build',['lake','build','LeanCert.API.Bounds'],cwd=core,phase='setup')
    env={'LEAN_PATH':str(ROOT/'.lake/build/lib/lean')}
    results=[]
    for name in ['Probe','Composition','ModuleBoundary','AffineKernel']:
        shutil.copyfile(FIXTURES/(name+'.lean.txt'),core/(name+'.lean'))
        label=name.lower();expected=name in ['ModuleBoundary','AffineKernel']
        try:
            text=runner.run(label,['lake','env','lean',name+'.lean'],cwd=core,env=env)
        except RuntimeError:
            text=(out/'runs'/label/'stdout.txt').read_text()
            marker='cannot import non-`module`' if name=='ModuleBoundary' else 'failed to reduce'
            if not expected or marker not in text:raise
            results.append({'case':name,'status':'expected_rejection'})
        else:
            if expected:raise AssertionError('Expected integration rejection: '+name)
            if name=='Composition':
                found=re.search(r"'LeanCertTrial.accuracy' depends on axioms: \[(.*?)\]",text)
                if found is None or set(found[1].split(', '))!={'propext','Classical.choice','Quot.sound'}:
                    raise AssertionError('Unapproved or missing axiom audit in composition control')
            results.append({'case':name,'status':'kernel_checked'})
            # Frozen source recheck; no discovery tactic or producer is involved.
            runner.run(label+'-replay',['lake','env','lean',name+'.lean'],cwd=core,env=env)
    measured=metrics(out)
    measured['lean_source_bytes']=sum((core/(name+'.lean')).stat().st_size for name in ['Probe','Composition','ModuleBoundary','AffineKernel'])
    save(out/'results.json',{'revision':PINS['leancert']['revision'],'cases':results,**measured})


def daisy(source,java,z3,out,input_errors):
    revision=source_pin(source,'daisy')
    patch_path=ROOT/PINS['daisy']['patch']
    subprocess.run(['git','-C',str(source),'apply','--reverse','--check',str(patch_path)],check=True)
    relative='src/main/scala/daisy/backend/InfoPhase.scala'
    original=subprocess.check_output(['git','-C',str(source),'show','HEAD:'+relative],text=True)
    expected=original.replace('absError.map(_.toString).getOrElse("")','absError.map(e => s"${e.n}/${e.d}").getOrElse("")')
    if (source/relative).read_text()!=expected:raise ValueError('Unexpected Daisy export patch')
    tool=source/'daisy'
    if not tool.is_file():raise ValueError('Build the pinned patched Daisy source first')
    compiled=hashlib.sha256()
    for path in sorted((source/'target/scala-2.13/classes').rglob('*.class')):
        compiled.update(str(path.relative_to(source)).encode());compiled.update(path.read_bytes())
    compiled_identity=compiled.hexdigest()
    admission=Runner(out)
    admission.run('java-version',[java/'java','-version'],phase='admission')
    admission.run('z3-version',[z3/'z3','--version'],phase='admission')
    def rat(value):
        value=Q(value)
        if value.denominator!=1 or abs(value)>2**53:
            raise ValueError('Trial admits exact small integer literals only')
        return str(value.numerator)+'.0'
    def produce(session):
        applicable(session.program,session.request)
        if len(session.program.outputs)!=1:raise ValueError('Trial requires one output')
        root=session.output/'producer';root.mkdir();(root/'output').mkdir()
        shutil.copytree(source/'library',root/'library')
        program=session.program;request=session.request
        args=', '.join('a'+str(i)+': Real' for i,_ in enumerate(program.inputs))
        requires=' && '.join(rat(request['domain'][n][0])+' <= a'+str(i)+' && a'+str(i)+' <= '+rat(request['domain'][n][1]) for i,n in enumerate(program.inputs))
        if input_errors=='exact':
            requires+=' && '+ ' && '.join('(a'+str(i)+' +/- 0.0)' for i,_ in enumerate(program.inputs))
        lines=['import daisy.lang._','import Real._','object FlareTrial {',
               'def kernel('+args+'): Real = {','require('+requires+')']
        for node in program.nodes:
            expr=rat(Q.from_float(number(node.bits))) if node.op=='constant' else node_expression(node)
            lines.append('val '+node.name+': Real = '+expr)
        query=root/'query.scala';query.write_text('\n'.join([*lines,program.outputs[0],'}','}'])+'\n')
        options=['--precision=Float64','--rangeMethod=interval','--errorMethod=affine',
                 '--results-csv=candidates.csv']
        if input_errors=='conservative':options+=['--noInitialErrors']
        if request['function']=='regularized_gain':options+=['--subdiv','--divLimit=3','--totalOpt=32']
        session.runner.run('daisy-output',[tool,*options,query],cwd=root,
            env={'PATH':os.pathsep.join([str(java),str(z3),os.environ['PATH']])},phase='analysis')
        rows=list(csv.DictReader((root/'output/candidates.csv').read_text().splitlines(),delimiter=';'))
        if len(rows)!=1 or rows[0]['Function name'].strip()!='kernel':
            raise ValueError('Expected exactly the selected Daisy function')
        raw=rows[0][' Absolute error'].strip()
        if '/' not in raw or Q(raw)<0:raise ValueError('Exact nonnegative rational export required')
        details={'tool':'daisy','revision':revision,'raw_candidate_bounds':[str(Q(raw))],
                 'patch_sha256':hashlib.sha256(patch_path.read_bytes()).hexdigest(),
                 'launcher_sha256':hashlib.sha256(tool.read_bytes()).hexdigest(),
                 'compiled_classes_sha256':compiled_identity,
                 'java_executable_sha256':hashlib.sha256((java/'java').read_bytes()).hexdigest(),
                 'z3_executable_sha256':hashlib.sha256((z3/'z3').read_bytes()).hexdigest(),
                 'input_error_mode':input_errors, 'evidence_form':'exact-rational-candidates','foreign_trace_checked':False}
        proposal=scalar.proposal(program,request,[str(Q(raw))],details)
        return proposal,proposal.details
    selected=registry.adapters();selected['daisy']=Adapter('daisy','producer',
        'numeric-candidates','Evaluation-only exact Daisy candidate producer',produce)
    cases={
        'addition':('def f(x,y):\n    return x+y\n',{'x':['-1','1'],'y':['-1','1']},'x+y'),
        'polynomial':('def f(x):\n    return x*x+x+1.0\n',{'x':['0','1']},'x*x+x+1'),
        'division':('def f(x):\n    return 1.0/x\n',{'x':['1','2']},'1/x'),
        'reciprocal':((ROOT/'examples/numerics/enclosures/energy.py').read_text(),{'x':['-1','1']},'1/(x*x+1)')}
    results=[]
    with patch.object(registry,'adapters',return_value=selected):
        for name,(text,domain,spec) in cases.items():
            case=out/name;case.mkdir();(case/'source.py').write_text(text)
            save(case/'request.json',{'schema':'numerics-request-v1','language':'python',
                'source':'source.py','function':'regularized_gain' if name=='reciprocal' else 'f',
                'producer':'daisy','domain':domain,'specification':[spec],
                'outputs':[{'name':'value','unit':'1','limit':'1/1099511627776'}]})
            results.append({'case':name,**checked_run(case/'request.json',case/'run')})
            save(out/'results.json',results)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('trial',choices=['leancert','daisy','typed'])
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--source',type=Path)
    parser.add_argument('--input-errors',choices=['exact','conservative'],default='exact')
    parser.add_argument('--java-bin',type=Path)
    parser.add_argument('--z3-bin',type=Path)
    args=parser.parse_args()
    if args.trial!='typed' and args.source is None:parser.error('--source is required for external trials')
    if args.trial=='daisy' and (args.java_bin is None or args.z3_bin is None):
        parser.error('Daisy requires --java-bin and --z3-bin')
    out=args.out.resolve();out.mkdir(parents=True,exist_ok=False)
    os.environ.setdefault('LAKE_ARTIFACT_CACHE','true')
    os.environ.setdefault('LAKE_RESTORE_ARTIFACTS','true')
    os.environ.setdefault('MATHLIB_NO_CACHE_ON_UPDATE','1')
    os.environ.setdefault('LEAN_NUM_THREADS','2')
    if args.trial=='typed':typed(out)
    elif args.trial=='leancert':leancert(args.source.resolve(),out)
    else:daisy(args.source.resolve(),args.java_bin.resolve(),args.z3_bin.resolve(),out,args.input_errors)


if __name__=='__main__':main()
