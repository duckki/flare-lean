"""Optional Rust extraction tools; no application checkout or core Lake dependency."""
import os
from pathlib import Path
import shutil

from numerics.emit.scalar import rust_source
from numerics.integrations.registry import ToolError


def model_files(path):
    from numerics.workflow.certification import sha
    return {str(p.relative_to(path)):sha(p) for p in sorted(path.rglob('*.olean*')) if p.is_file()}


def tools(request, proof_only=False):
    selection=request.get('rust_tools',{})
    if not isinstance(selection,dict) or set(selection)-{'charon','aeneas','lean_lib'}:
        raise ValueError('rust_tools supports charon, aeneas and lean_lib paths')
    names=['lean_lib'] if proof_only else ['charon','aeneas','lean_lib']
    result={}
    for name in names:
        value=selection.get(name) or os.environ.get('FLARE_'+('AENEAS_LEAN_LIB' if name=='lean_lib' else name.upper()))
        if not value and name!='lean_lib': value=shutil.which(name)
        if not value:
            raise ToolError('missing_tool', 'Missing optional Rust tool '+name+'; configure rust_tools or FLARE_'+name.upper())
        path=Path(value).expanduser().resolve()
        if name=='lean_lib':
            if not (path/'Aeneas.olean').is_file(): raise ToolError('missing_tool', 'Missing compiled Aeneas.olean in '+str(path))
        elif not path.is_file() or not os.access(path,os.X_OK):
            raise ToolError('missing_tool', 'Rust tool is not executable: '+str(path))
        result[name]=path
    return result


def extract(program, source, request, output, work, runner):
    from numerics.workflow.certification import ROOT, save, sha
    selected=tools(request)
    crate=output/'rust'; (crate/'src').mkdir(parents=True)
    (crate/'Cargo.toml').write_text('[package]\nname="numerics-kernel"\nversion="0.1.0"\nedition="2021"\n\n[lib]\npath="src/lib.rs"\n\n[workspace]\n')
    (crate/'rust-toolchain.toml').write_bytes((ROOT/'provider/manifests/rust-toolchain.toml').read_bytes())
    if program.language=='rust' or request.get('rust_port'):
        port = request.get('rust_port')
        if port:
            source = (output/'rust-port.rs').read_bytes()
        function = port['function'] if port else program.function
        (crate/'src/original.rs').write_bytes(source)
        params=', '.join(f'a{i}: f64' for i in range(len(program.inputs)))
        args=', '.join(f'a{i}' for i in range(len(program.inputs)))
        typ='f64' if len(program.outputs)==1 else '(f64, f64)'
        if program.scientific:
            from numerics.frontends.scientific import count
            call_args=[];offset=0
            for field in program.scientific['inputs']:
                size=count(field['shape'])
                def aggregate(dims,base):
                    if not dims:return 'a'+str(base)
                    step=count(dims[1:])
                    return '['+', '.join(aggregate(dims[1:],base+j*step) for j in range(dims[0]))+']'
                call_args.append(aggregate(field['shape'],offset));offset+=size
            from numerics.emit.scalar import returned
            values=[]
            for i,shape in enumerate(program.scientific['outputs']):
                base='result' if len(program.scientific['outputs'])==1 else 'result.'+str(i)
                from numerics.frontends.python_arrays import paths
                values += [base+''.join('['+str(j)+']' for j in index) for index in paths(shape)]
            code=f'mod original;\npub fn kernel({params}) -> {typ} {{\n    let result = original::{function}('+', '.join(call_args)+');\n    '+returned(values)+'\n}\n'
        else:
            code=f'mod original;\npub fn kernel({params}) -> {typ} {{ original::{function}({args}) }}\n'
    else:
        code=rust_source(program)
    (crate/'src/lib.rs').write_text(code)
    save(output/'rust-tools.json',{n:{'path':str(p),'sha256':sha(p) if p.is_file() else sha(p/'Aeneas.olean')}
                                  for n,p in selected.items()})
    save(output/'aeneas-model.json',model_files(selected['lean_lib']))
    runner.run('rust-version',['rustc','-Vv'],cwd=crate,phase='admission')
    llbc=work/'input.llbc'
    runner.run('extract',[selected['charon'],'cargo','--preset=aeneas','--sysroot=default',
        '--start-from','numerics_kernel::kernel','--dest-file='+str(llbc),'--','--lib'],
        cwd=crate,env={'CARGO_TARGET_DIR':str(work/'native')})
    shutil.copyfile(llbc,output/'input.llbc')
    lean=output/'lean';lean.mkdir(exist_ok=True)
    runner.run('translate',[selected['aeneas'],'-backend','lean','-abort-on-error','-warnings-as-errors',
        llbc,'-dest',lean,'-subdir','/Workflow/Generated','-split-files','-namespace','Workflow.Generated'])


def imported_model(path, modules):
    """Identity of exactly the compiled model modules loaded by a checked root."""
    from numerics.workflow.certification import sha
    selected, files = [], {}
    for module in sorted(set(modules)):
        relative = Path(*module.split('.')).with_suffix('.olean')
        source = path/relative
        if not source.is_file():
            continue
        selected.append(module)
        for suffix in ('', '.private', '.server'):
            artifact = Path(str(source)+suffix)
            if not artifact.is_file():
                raise ValueError('Incomplete imported Aeneas module: '+module)
            files[str(artifact.relative_to(path))] = sha(artifact)
    if 'Aeneas' not in selected:
        raise ValueError('Checked root did not load the Aeneas model')
    return {'schema': 'numerics-imported-model-v1', 'modules': selected, 'files': files}


def matching_model(path, recorded):
    """Allow unrelated model build products; preserve legacy complete manifests."""
    if recorded.get('schema') == 'numerics-imported-model-v1':
        return imported_model(path, recorded['modules']) == recorded
    return model_files(path) == recorded
