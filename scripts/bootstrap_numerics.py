#!/usr/bin/env python3
"""Bootstrap a supplied FLARE provider into explicit user tool/artifact locations.

Requires Python, curl, Git, Make and the platform C/C++ build prerequisites.
Does not install system packages, alter shell profiles or change an application.
"""
import argparse
import json
import math
import os
from pathlib import Path
import platform
import shutil
import sys
import tarfile
import time

from numerics.workflow import ROOT, Runner, save, sha


TOOLS=['lean','lake','elan','gappa','fptaylor','precisa','charon','aeneas','rustc','cbmc']


def baseline():
    return {'system':platform.system(),'architecture':platform.machine(),'python':sys.version,
            'tools':{name:shutil.which(name) for name in TOOLS}}


def unpack_elan(archive,directory):
    with tarfile.open(archive) as stream:
        files=[m for m in stream.getmembers() if m.name.lstrip('./')=='elan-init']
        if len(files)!=1 or not files[0].isfile():raise ValueError('Expected one regular elan-init release executable')
        target=directory/'elan-init'
        with stream.extractfile(files[0]) as source:target.write_bytes(source.read())
        target.chmod(0o755)
    return target


def bootstrap(provider,tools,output,packages=(),timeout=1800,require_clean=False,skill=None,shared_cache=False):
    if type(timeout) not in (int,float) or not math.isfinite(timeout) or timeout<=0:
        raise ValueError('Bootstrap timeout must be finite and positive')
    provider=Path(provider).resolve();tools=Path(tools).expanduser().resolve();output=Path(output).resolve()
    if any(not (provider/name).is_file() for name in ['lean-toolchain','lake-manifest.json','scripts/certify_numerics.py','skills/verify-numerics/SKILL.md']):
        raise ValueError('Expected a complete supplied FLARE provider')
    if tools.is_relative_to(provider) or output==provider or output==tools or output.is_relative_to(tools) or tools.is_relative_to(output):
        raise ValueError('Use a tool pool outside the provider and a separate receipt directory')
    recipe=json.loads((provider/'tools/numerics/bootstrap.json').read_text())
    if set(packages)-set(recipe['packages']):raise ValueError('Unsupported bootstrap package')
    initial=baseline()
    if require_clean and any(initial['tools'].values()):raise ValueError('Clean bootstrap requires no verification tools on PATH')
    if require_clean and tools.exists() and any(tools.iterdir()):raise ValueError('Clean bootstrap requires an empty tool destination')
    if skill is not None and sha(skill)!=sha(provider/'skills/verify-numerics/SKILL.md'):
        raise ValueError('Skill/provider mismatch; obtain the matching complete provider or supplied source bundle')
    if (tools/'elan').exists():raise ValueError('Tool destination exists; preserve it and use a new bootstrap destination')
    output.mkdir(parents=True,exist_ok=False);tools.mkdir(parents=True,exist_ok=True)
    runner=Runner(output,timeout);started=time.monotonic()
    environment={'ELAN_HOME':str(tools/'elan'),'PATH':str(tools/'elan/bin')+os.pathsep+os.environ.get('PATH',''),
                 'MATHLIB_NO_CACHE_ON_UPDATE':'1','LEAN_NUM_THREADS':'2'}
    if shared_cache:environment.update(LAKE_ARTIFACT_CACHE='true',LAKE_RESTORE_ARTIFACTS='true')
    record={'bootstrap_sha256':sha(Path(__file__)),'runner_sha256':sha(ROOT/'scripts/tool_integration_run.py'),
            'schema':'numerics-bootstrap-v1','status':'unresolved','baseline':initial,
            'provider':str(provider),'tools':str(tools),'requested_packages':list(packages),
            'provider_inputs':{name:sha(provider/name) for name in ['lean-toolchain','lake-manifest.json','skills/verify-numerics/SKILL.md','tools/numerics/bootstrap.json']},
            'environment':environment,'qualification':'Clean means absent from the recorded baseline PATH and an empty selected tool destination. VM/container/user isolation is recorded by the caller, not inferred here.'}
    save(output/'bootstrap.json',record)
    try:
        key=initial['system']+'-'+initial['architecture']
        if key not in recipe['elan']['assets']:raise ValueError('No pinned Elan bootstrap asset for '+key)
        name,digest=recipe['elan']['assets'][key];archive=output/name
        url=recipe['elan']['repository']+'/releases/download/'+recipe['elan']['version']+'/'+name
        runner.run('elan-download',['curl','--fail','--location','--retry','3',url,'--output',archive],phase='setup')
        if sha(archive)!=digest:raise ValueError('Elan archive differs from the official pinned release digest')
        record['elan_asset']={'url':url,'sha256':digest}
        installer=unpack_elan(archive,output)
        runner.run('elan-install',[installer,'-y','--no-modify-path','--default-toolchain','none'],env=environment,phase='setup')
        toolchain=(provider/'lean-toolchain').read_text().strip()
        runner.run('lean-install',['elan','toolchain','install',toolchain],cwd=provider,env=environment,phase='setup')
        for package in packages:
            version=recipe['packages'][package];destination=tools/(package+'-'+version)
            if destination.exists():raise ValueError('Package destination exists; preserve it and choose a new tool pool')
            downloads=output/(package+'-downloads');downloads.mkdir()
            runner.run(package+'-download',[sys.executable,'-m','pip','download','--no-deps','--only-binary=:all:',
                '--dest',downloads,package+'=='+version],phase='setup')
            wheels=list(downloads.glob('*.whl'))
            if len(wheels)!=1:raise ValueError('Expected one pinned '+package+' wheel')
            metadata=output/(package+'-pypi.json')
            runner.run(package+'-metadata',['curl','--fail','--location','https://pypi.org/pypi/'+package+'/'+version+'/json',
                '--output',metadata],phase='setup')
            published=json.loads(metadata.read_text())
            expected={v['filename']:v['digests']['sha256'] for v in published['urls']}
            if expected.get(wheels[0].name)!=sha(wheels[0]):raise ValueError('Wheel differs from the official PyPI digest')
            runner.run(package+'-install',[sys.executable,'-m','pip','install','--no-deps','--target',destination,wheels[0]],phase='setup')
            environment['FLARE_NUMPY' if package=='numpy' else 'FLARE_C_PARSER']=str(destination)
            record.setdefault('packages',{})[package]={'version':version,'wheel':wheels[0].name,'sha256':sha(wheels[0])}
        runner.run('dependencies',['lake','env','lean','--version'],cwd=provider,env=environment,phase='setup')
        # This is an explicit cold-pool bootstrap, never an ordinary-project update.
        runner.run('mathlib-bootstrap',['lake','exe','cache','get','Flare.*'],cwd=provider,env=environment,phase='setup')
        runner.run('flare-build',['lake','build','Flare'],cwd=provider,env=environment,phase='setup')
        record.update(status='installed',toolchain=toolchain)
        save(output/'environment.json',environment)
    except (RuntimeError,ValueError,OSError) as error:
        record.update(error=str(error),failure_stage=getattr(runner,'last_stage','admission'))
        raise
    finally:
        record['seconds']=time.monotonic()-started;save(output/'bootstrap.json',record)
    return record


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--provider',type=Path,default=ROOT)
    parser.add_argument('--tools',required=True,type=Path)
    parser.add_argument('--out',required=True,type=Path)
    parser.add_argument('--package',choices=['numpy','pycparser'],action='append',default=[])
    parser.add_argument('--timeout',type=float,default=1800)
    parser.add_argument('--require-clean',action='store_true')
    parser.add_argument('--skill',type=Path)
    parser.add_argument('--shared-cache',action='store_true')
    args=parser.parse_args()
    try:
        result=bootstrap(args.provider,args.tools,args.out,args.package,args.timeout,args.require_clean,args.skill,args.shared_cache)
        print(json.dumps({'status':result['status'],'receipt':str(args.out/'bootstrap.json')},indent=2));return 0
    except (ValueError,RuntimeError,OSError) as error:
        print(json.dumps({'status':'setup_failed','error':str(error)},indent=2));return 2


if __name__=='__main__':sys.exit(main())
