"""Actual source-runtime admission and batch bit-pattern diagnostics."""
import json
from pathlib import Path
import re
import shutil
import sys

from .frontend import FRONTENDS, word


def validate_selection(program, selection):
    if selection is None:
        return
    if not isinstance(selection, dict) or set(selection) - {'kind', 'executable'}:
        raise ValueError('source_runtime must contain kind and optional executable')
    allowed = FRONTENDS[program.language].runtimes or ('python',)
    if selection.get('kind') not in allowed:
        raise ValueError('Source runtime must be one of: '+', '.join(allowed))
    if 'executable' in selection and (not isinstance(selection['executable'], str) or not selection['executable'].strip()):
        raise ValueError('source_runtime.executable must be a nonempty executable path')
    if program.language == 'python' and 'executable' in selection:
        raise ValueError('Python currently uses the orchestrator interpreter; run the CLI with that interpreter')


def runtime_candidates(language):
    if language == 'python':
        return {'python': sys.executable}
    return {name: shutil.which(name) for name in FRONTENDS[language].runtimes}


def runtime_selection(program, request):
    selection = request.get('source_runtime')
    validate_selection(program, selection)
    if program.language == 'python':
        return {'kind': 'python', 'executable': sys.executable, 'version': sys.version}
    allowed = FRONTENDS[program.language].runtimes
    kind = selection['kind'] if selection else next((x for x in allowed if shutil.which(x)), allowed[0])
    executable = shutil.which(selection.get('executable', kind) if selection else kind)
    if not executable:
        raise RuntimeError(f'Missing source runtime {kind}; provide source_runtime.kind and executable or install it on PATH. Source-runtime validation cannot be replaced by graph execution.')
    # Preserve launcher names: rustup chooses rustc from argv[0].
    return {'kind': kind, 'executable': str(Path(executable).absolute())}


def matlab_string(value):
    return "'"+str(value).replace("'", "''")+"'"


def julia_string(value):
    # JSON and Julia strings differ on interpolation syntax.
    return json.dumps(str(value), ensure_ascii=True).replace('$', r'\$')


def command(runtime, script=None):
    exe, kind = runtime['executable'], runtime['kind']
    if kind == 'rustc':
        return [exe, '-Vv']
    if kind in ('clang','gcc'):
        return [exe, '--version']
    if kind == 'julia':
        return [exe, '--startup-file=no', '--history-file=no', '--math-mode=ieee', '--threads=1',
                '--color=no', *([str(script)] if script else ['--version'])]
    if kind == 'octave':
        return [exe, '--no-init-file', '--no-site-file', '--no-gui', '--quiet', '--no-history',
                *([str(script)] if script else ['--version'])]
    if kind == 'matlab':
        expression = 'run('+matlab_string(script)+')' if script else 'disp(version)'
        return [exe, '-batch', expression]
    raise ValueError('No external source-runtime command for '+kind)


def admit_runtime(program, request, output, work, runner):
    runtime = runtime_selection(program, request)
    if program.language=='c' and sys.platform=='darwin' and runtime['kind']=='clang':
        selected=runner.run('source-compiler-path',[runtime['executable'],'-print-prog-name=clang'],
                           cwd=work,phase='admission',inherit_developer_dir=True).strip()
        if Path(selected).is_absolute() and Path(selected).is_file():
            runtime['launcher']=runtime['executable'];runtime['executable']=selected
        runtime['sdk']=runner.run('source-sdk',['/usr/bin/xcrun','--show-sdk-path'],
                                  cwd=work,phase='admission',inherit_developer_dir=True).strip()
    if runtime['kind'] != 'python':
        env = {'JULIA_DEPOT_PATH': str(work/'julia-depot')} if runtime['kind'] == 'julia' else {}
        runtime['version'] = runner.run('source-version', command(runtime), cwd=work, env=env, phase='admission',
                                       **({'inherit_developer_dir':True} if program.language=='c' else {})).strip()
    from .workflow import save, sha
    runtime['executable_sha256'] = sha(runtime['executable'])
    runtime['qualification'] = 'Actual selected interpreter; runtime/compiler semantics remain trusted. Octave is not evidence of MATLAB runtime execution.'
    if program.language=='c':
        runtime['qualification']='Actual selected C compiler and SDK; compiler/runtime fidelity remains trusted. c-runtime.json records original-source compiler modes, flags and sanitizer configuration.'
    if program.scientific:
        from .scientific_runtime import admit as admit_scientific
        admit_scientific(program,runtime)
    save(output/'source-runtime.json', runtime)
    return runtime


def julia_driver(program, root):
    if program.scientific:
        from .scientific_runtime import julia_driver as scientific_driver
        return scientific_driver(program,root)
    return f'''module WorkflowSource
include({julia_string(root/'source.jl')})
end
let
    tiny = reinterpret(Float64, UInt64(1))
    @assert tiny * 1.0 == tiny
    @assert 1.0 + 2.0^(-53) == 1.0
    open({julia_string(root/'results.hex')}, "w") do output
        for line in eachline({julia_string(root/'inputs.hex')})
            args = [reinterpret(Float64, parse(UInt64, x; base=16)) for x in split(line)]
            value = WorkflowSource.{program.function}(args...)
            values = value isa Tuple ? value : (value,)
            @assert length(values) == {len(program.outputs)}
            @assert all(x -> typeof(x) === Float64, values)
            println(output, join([string(reinterpret(UInt64, x); base=16, pad=16) for x in values], " "))
        end
    end
end
'''


def matlab_driver(program, root):
    names = [f'workflow_out{i}' for i in range(len(program.outputs))]
    lhs = names[0] if len(names) == 1 else '['+', '.join(names)+']'
    lines = [f'addpath({matlab_string(root)});',
        "workflow_tiny = hex2num('0000000000000001');",
        'assert(workflow_tiny * 1.0 == workflow_tiny);',
        'assert(1.0 + 2.0^(-53) == 1.0);',
        f"workflow_rows = strsplit(strtrim(fileread({matlab_string(root/'inputs.hex')})), '\n');",
        f"workflow_file = fopen({matlab_string(root/'results.hex')}, 'w');",
        'assert(workflow_file >= 0);', 'workflow_cleanup = onCleanup(@() fclose(workflow_file));',
        'for workflow_i = 1:numel(workflow_rows)',
        '  workflow_words = strsplit(strtrim(workflow_rows{workflow_i}));',
        '  workflow_args = cellfun(@hex2num, workflow_words, \'UniformOutput\', false);',
        f'  {lhs} = WorkflowSource.{program.function}(workflow_args{{:}});']
    for name in names:
        lines += [f"  assert(isa({name}, 'double') && isreal({name}) && isscalar({name}));"]
    lines += [f"  fprintf(workflow_file, '%s', num2hex({names[0]}));"]
    lines += [f"  fprintf(workflow_file, ' %s', num2hex({name}));" for name in names[1:]]
    lines += ["  fprintf(workflow_file, '\n');", 'end', 'clear workflow_cleanup;']
    # MATLAB string literals contain backslash-n characters, not actual newlines.
    return '\n'.join(lines).replace("'\n'", "'\\n'")+'\n'


def source_results(program, source, cases, runtime, output, work, runner, request=None):
    """Execute the original admitted source, never the common graph as its proxy."""
    request = request or {}
    adapter = FRONTENDS[program.language]
    if program.scientific and program.language=='python':
        from .scientific_runtime import python_results
        return python_results(program,source,cases)
    if adapter.load_for_diagnostics is not None:
        if request.get("python_method") is not None:
            from .python_method import load_method
            function = load_method(source, program.function, request["python_method"])
        elif program.counted:
            from .python_counted import load_counted
            function=load_counted(source,program)
        elif program.arrays:
            from .python_arrays import load_arrays
            function = load_arrays(source,program.function,program.arrays)
        else:
            function = adapter.load_for_diagnostics(source, program.function)
        rows = []
        from .frontend import number
        for case in cases:
            value = function(*(number(x) for x in case))
            values = value if isinstance(value, tuple) else (value,)
            if len(values) != len(program.outputs) or any(type(x) is not float for x in values):
                raise ValueError('Original Python must return the declared number of built-in float scalars')
            rows.append(tuple(word(x) for x in values))
        return rows
    root = output/'source-diagnostics'
    root.mkdir()
    (root/'inputs.hex').write_text('\n'.join(' '.join(f'{x:016x}' for x in case) for case in cases)+'\n')
    if program.language == 'c':
        from .c_runtime import source_results as c_results
        return c_results(program,source,cases,runtime,output,work,runner)
    if program.language == 'rust':
        (root/'source.rs').write_text(source)
        args=', '.join(f'f64::from_bits(w[{i}])' for i in range(len(program.inputs)))
        values=['v'] if len(program.outputs)==1 else ['v.0','v.1']
        script=root/'driver.rs'
        script.write_text('use std::io::{self,BufRead};\nmod original { include!('+json.dumps(str(root/'source.rs'),ensure_ascii=False)+'); }\nfn main() { for line in io::stdin().lock().lines() { let line=line.unwrap(); let w:Vec<u64>=line.split_whitespace().map(|s|u64::from_str_radix(s,16).unwrap()).collect(); let v=original::'+program.function+'('+args+'); println!(\"'+' '.join(['{:016x}']*len(values))+'\", '+', '.join(v+'.to_bits()' for v in values)+'); }}\n')
        binary=work/'source-runtime'
        runner.run('source-compile',[runtime['executable'],'--edition=2021',script,'-o',binary],cwd=work,phase='diagnostic')
        wrapper=work/'source-runtime.py'
        wrapper.write_text('import subprocess\nfrom pathlib import Path\np=subprocess.run(['+repr(str(binary))+'],input=Path('+repr(str(root/'inputs.hex'))+').read_bytes(),capture_output=True,check=True)\nPath('+repr(str(root/'results.hex'))+').write_bytes(p.stdout)\n')
        runner.run('source-execute',[sys.executable,wrapper],cwd=work,phase='diagnostic')
    elif program.language == 'julia':
        (root/'source.jl').write_text(source)
        script = root/'driver.jl'
        script.write_text(julia_driver(program, root))
    else:
        package = root/'+WorkflowSource'
        package.mkdir()
        (package/(program.function+'.m')).write_text(source)
        script = root/'driver.m'
        script.write_text(matlab_driver(program, root))
    if program.language != 'rust':
        env = {'JULIA_DEPOT_PATH': str(work/'julia-depot')} if runtime['kind'] == 'julia' else {}
        runner.run('source-execute', command(runtime, script), cwd=work, env=env, phase='diagnostic')
    rows = [line.split() for line in (root/'results.hex').read_text().splitlines()]
    if (len(rows) != len(cases) or any(len(row) != len(program.outputs) for row in rows)
            or any(not re.fullmatch('[0-9a-fA-F]{16}', x) for row in rows for x in row)):
        raise ValueError('Source runtime returned malformed or incomplete word results')
    return [tuple(int(x, 16) for x in row) for row in rows]
