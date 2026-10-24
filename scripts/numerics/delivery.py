"""Portable frozen evidence and explicit change-aware rechecking.

Archive hashes detect corruption, not provenance. Only fresh root reconstruction,
Lean checking and the axiom audit establish the delivered certificate.
"""
import io
import json
from pathlib import Path, PurePosixPath
import shutil
import tarfile
import tempfile

from .workflow import Runner, audit_run, dependencies, prepare, replay_run, save, sha


MAX_BYTES=2_000_000_000


def member_name(name):
    path=PurePosixPath(name)
    if not name or path.is_absolute() or any(x in ('','.','..') for x in name.split('/')) or '\\' in name:
        raise ValueError('Bundle contains an unsafe or noncanonical path')
    return path


def pack(run,archive):
    run=Path(run).resolve();archive=Path(archive).resolve()
    if archive.is_relative_to(run):raise ValueError('Store the bundle outside its input run')
    audit_run(run,frozen=True)
    result=json.loads((run/'result.json').read_text())
    if result.get('status') not in ('certified','counterexample','budget_not_met') or 'lean_root_checked' not in result.get('completed_stages',[]):
        raise ValueError('Only completed Lean roots can be bundled')
    files={}
    for path in sorted(run.rglob('*')):
        if path.is_symlink():raise ValueError('Portable bundles cannot contain symbolic links')
        if path.is_file():files[str(path.relative_to(run))]=sha(path)
    if sum((run/name).stat().st_size for name in files)>MAX_BYTES:raise ValueError('Bundle exceeds 2 GB limit')
    manifest=json.dumps({'schema':'numerics-bundle-v1','files':files},sort_keys=True).encode()
    archive.parent.mkdir(parents=True,exist_ok=True)
    try:
        with archive.open('xb') as output,tarfile.open(fileobj=output,mode='w:gz',dereference=True) as stream:
            info=tarfile.TarInfo('bundle.json');info.size=len(manifest);stream.addfile(info,io.BytesIO(manifest))
            for name in files:stream.add(run/name,arcname='run/'+name,recursive=False)
    except BaseException:
        # Never delete an archive that existed before this invocation.
        if 'output' in locals():archive.unlink(missing_ok=True)
        raise
    return {'status':'bundled','archive':str(archive),'sha256':sha(archive),'files':len(files),
            'qualification':'Frozen evidence only; a recipient must replay its Lean root with matching proof dependencies.'}


def unpack(archive,output):
    output=Path(output).resolve()
    if output.exists():raise ValueError('Choose a new bundle destination')
    output.parent.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='flare-bundle-',dir=output.parent) as directory:
        temporary=Path(directory)
        with tarfile.open(archive) as stream:
            members=[];seen=set();total=0
            for member in stream:
                members.append(member)
                member_name(member.name)
                if member.name in seen or not member.isfile():raise ValueError('Bundle entries must be unique regular files')
                seen.add(member.name);total+=member.size
                if total>MAX_BYTES or len(seen)>20000:raise ValueError('Bundle resource limit exceeded')
            headers=[m for m in members if m.name=='bundle.json']
            if len(headers)!=1 or headers[0].size>10_000_000:raise ValueError('Missing or oversized bundle manifest')
            manifest=json.load(stream.extractfile(headers[0]))
            if not isinstance(manifest,dict) or set(manifest)!={'schema','files'} or manifest['schema']!='numerics-bundle-v1' or not isinstance(manifest['files'],dict):
                raise ValueError('Expected numerics-bundle-v1 manifest')
            files=manifest['files']
            for name in files:member_name(name)
            if seen!={'bundle.json',*('run/'+name for name in files)}:raise ValueError('Bundle manifest and payload differ')
            for member in members:
                if member.name=='bundle.json':continue
                name=member.name[4:];target=temporary/name;target.parent.mkdir(parents=True,exist_ok=True)
                with stream.extractfile(member) as source,target.open('xb') as destination:
                    shutil.copyfileobj(source,destination)
                if sha(target)!=files[name]:raise ValueError('Bundle payload hash mismatch: '+name)
        audit_run(temporary,frozen=True)
        shutil.move(str(temporary),output)
    return {'status':'unpacked','run':str(output),
            'qualification':'Integrity audit only. Run replay to reconstruct and check the Lean root; archive hashes are not authentication.'}


def contract(request,base,active=()):
    # Paths become content identities; operational tools/runtime locations do not
    # change the frozen theorem. A new runtime still needs fresh diagnostics.
    base=Path(base).resolve()
    operational={'source','source_runtime','analysis_tools','search_tools','rust_tools',
                 'rust_runtime','timeout_seconds','contract_cache'}
    result={k:v for k,v in request.items() if k not in operational}
    for field,paths in [('proof',('source',)),('rust_port',('source','proof_source'))]:
        if field in result:
            result[field]={**result[field],**{name:sha(base/result[field][name]) for name in paths}}
    if 'rust_application' in result:
        bundle=dict(result['rust_application'])
        for field in ('files','lean_modules','licenses'):
            if field in bundle:bundle[field]={name:sha(base/path) for name,path in bundle[field].items()}
        components={}
        for name,path in bundle.get('components',{}).items():
            selected=(base/path).resolve()
            if selected in active or len(active)>16:raise ValueError('Cyclic or oversized component contract closure')
            child=json.loads(selected.read_text())
            components[name]={'source_sha256':sha(selected.parent/child['source']),
                'contract':contract(child,selected.parent,(*active,selected))}
        if 'components' in bundle:bundle['components']=components
        result['rust_application']=bundle
    return result


def recheck(run,request_path,output,aeneas_lean_lib=None):
    run=Path(run).resolve();output=Path(output).resolve()
    if output.exists():raise ValueError('Choose a new recheck destination')
    audit_run(run,frozen=True)
    old,old_source,old_program,old_questions=prepare(run/'request.json',replay=True)
    new,new_source,new_program,new_questions=prepare(request_path,replay=True)
    if old_questions or new_questions:raise ValueError('Recheck requires complete original and current requests')
    differences=[]
    if old_source.read_bytes()!=new_source.read_bytes():differences.append('source')
    if contract(old,run)!=contract(new,Path(request_path).resolve().parent):differences.append('contract or profile')
    if old_program.record()!=new_program.record():differences.append('source model')
    original=json.loads((run/'result.json').read_text());current=dependencies()
    changed=sorted(name for name in set(original['dependencies'])|set(current) if original['dependencies'].get(name)!=current.get(name))
    if 'lean-toolchain' in changed:differences.append('Lean toolchain')
    if old.get('target')=='rust-aeneas':
        from .rust import matching_model,tools
        selected=aeneas_lean_lib or str(tools(new,proof_only=True)['lean_lib'])
        if not matching_model(Path(selected),json.loads((run/'aeneas-model.json').read_text())):
            differences.append('Aeneas proof model')
        aeneas_lean_lib=selected
    result={'schema':'numerics-recheck-v1','status':'needs_reverification' if differences else 'rechecked',
        'changed_dependencies':changed,'incompatible_changes':differences,
        'runtime_diagnostics':'Frozen original diagnostics only; recheck does not execute source or validate a new runtime.',
        'qualification':'Source/contract/profile changes need a new verification run. Compatible provider changes require fresh Lean root reconstruction and checking.'}
    output.mkdir(parents=True)
    if not differences:
        # Rechecking source-level dependency identities against stale compiled
        # library artifacts would mislabel the provider being checked.
        stage='provider-build'
        try:
            timeout=new.get('timeout_seconds',240 if new.get('rust_application') else 120)
            Runner(output,timeout).run('provider-build',['lake','build','Flare'])
            stage='replay'
            replay=replay_run(run,output/'replay',aeneas_lean_lib,timeout_seconds=timeout)
            result['certificate_status']=replay['certificate_status'];result['entry_theorem']=replay['entry_theorem']
        except (ValueError,RuntimeError,OSError) as error:
            result.update(status='unresolved',error=str(error),failure_stage=stage)
    save(output/'recheck.json',result)
    return result
