"""Actual NumPy/Julia collection execution and versioned runtime identities."""
import importlib
import os
import re
from pathlib import Path
import sys

from numerics.integrations.registry import ToolError
from numerics.frontends.scientific import count


def numpy():
    try:module=importlib.import_module('numpy')
    except ImportError:
        cache=Path.home()/'Library/Caches/flare' if sys.platform=='darwin' else Path(os.environ.get('XDG_CACHE_HOME',Path.home()/'.cache'))/'flare'
        directory=Path(os.environ.get('FLARE_NUMPY',cache/'numpy-2.4.0'))
        if not (directory/'numpy').is_dir():raise ToolError('missing_tool','NumPy source diagnostics need numpy==2.4.0 in Python or '+str(directory))
        sys.path.insert(0,str(directory))
        try:module=importlib.import_module('numpy')
        except ImportError as error:raise ToolError('missing_tool','Cannot load the selected NumPy binary for this Python/platform: '+str(error)) from error
    if module.__version__!='2.4.0':raise ToolError('unsupported_tool_version','Scientific NumPy profile requires 2.4.0; run in a compatible isolated Python environment')
    return module


def admit(program,runtime):
    if program.language=='julia':
        if not re.search(r'(?<![\d.])1\.11\.7(?![\d.])',runtime['version']):raise ToolError('unsupported_tool_version','Scientific Julia profile requires Julia 1.11.7')
        return
    from numerics.workflow.certification import sha
    np=numpy();tiny=np.array([float.fromhex('0x0.0000000000001p-1022')],dtype=np.float64)
    with np.errstate(all='ignore'):
        if np.multiply(tiny,1.0)[0]!=tiny[0] or np.add(np.float64(1.0),2.0**-53)!=1.0:
            raise ToolError('unsupported_arithmetic','NumPy nearest/subnormal preflight failed')
    root=Path(np.__file__).parent
    files=[root/'__init__.py',root/'_core/numeric.py',*root.rglob('*.so'),*root.rglob('*.pyd')]
    libs=root.parent/'numpy.libs'
    if libs.exists():files += [p for p in libs.rglob('*') if p.is_file()]
    runtime['libraries']=[{'name':'numpy','version':np.__version__,'files':{str(p):sha(p) for p in sorted(set(files))}}]
    runtime['floating_error_policy']='Nontrapping; diagnostics use numpy.errstate(all=ignore). Status flags and warning/exception policy are outside the numerical theorem.'
    runtime['qualification']='Pinned ordinary native-endian float64 NumPy ndarray operations. Selected ufunc/indexing implementation, source mapping and compiler/hardware fidelity remain trusted; Lean proves the collection model and numerical root.'


def python_results(program,source,cases):
    from numerics.frontends.scalar import number, word
    np=numpy();namespace={};exec(compile(source,'<admitted-scientific-source>','exec'),namespace)
    fn=namespace[program.function];rows=[]
    for case in cases:
        offset=0;arguments=[]
        for field in program.scientific['inputs']:
            dims=field['shape'];values=[number(w) for w in case[offset:offset+count(dims)]];offset+=count(dims)
            value=np.array(values,dtype=np.float64).reshape(dims) if dims else float(values[0])
            if dims:value.setflags(write=False)
            arguments.append(value)
        with np.errstate(all='ignore'):result=fn(*arguments)
        values=result if isinstance(result,tuple) else (result,)
        if len(values)!=len(program.scientific['outputs']):raise ValueError('NumPy returned the wrong API structure')
        cells=[]
        for value,dims in zip(values,program.scientific['outputs'],strict=True):
            if dims:
                if type(value)is not np.ndarray or value.dtype!=np.dtype('float64') or not value.dtype.isnative or list(value.shape)!=dims:
                    raise ValueError('NumPy returned an incorrect shape/dtype')
                if any(isinstance(arg,np.ndarray) and np.shares_memory(value,arg) for arg in arguments):
                    raise ValueError('NumPy output unexpectedly aliases input storage')
                cells += [float(x) for x in value.ravel(order='C')]
            else:
                if type(value) not in (float,np.float64):raise ValueError('NumPy scalar output must be binary64')
                cells.append(float(value))
        rows.append(tuple(word(x) for x in cells))
    return rows


def julia_driver(program,root):
    from numerics.runtimes.source import julia_string
    args=[];offset=1
    for field in program.scientific['inputs']:
        size=count(field['shape'])
        args.append('Float64['+', '.join('args['+str(offset+j)+']' for j in range(size))+']' if field['shape'] else 'args['+str(offset)+']')
        offset+=size
    return f'''module WorkflowSource
include({julia_string(root/'source.jl')})
end
let
    @assert reinterpret(Float64, UInt64(1)) * 1.0 == reinterpret(Float64, UInt64(1))
    @assert 1.0 + 2.0^(-53) == 1.0
    open({julia_string(root/'results.hex')}, "w") do output
        for line in eachline({julia_string(root/'inputs.hex')})
            args = [reinterpret(Float64, parse(UInt64, x; base=16)) for x in split(line)]
            value = WorkflowSource.{program.function}({', '.join(args)})
            @assert typeof(value) === Vector{{Float64}} && length(value) == {len(program.outputs)}
            println(output, join([string(reinterpret(UInt64, x); base=16, pad=16) for x in value], " "))
        end
    end
end
'''
