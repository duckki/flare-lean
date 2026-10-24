"""Admit and diagnose selected binary32 storage / binary64 Python execution."""
from numerics.integrations.registry import ToolError
from numerics.runtimes.scientific import numpy


def admit(program,runtime):
    import platform
    import sys
    from numerics.frontends.scalar import word
    from numerics.runtimes.source import math_platform
    from numerics.runtimes.scientific import admit as admit_numpy
    if platform.python_implementation()!='CPython' or sys.version_info[:2] not in ((3,13),(3,14)):
        raise ToolError('unsupported_tool_version','Mixed storage requires CPython 3.13 or 3.14')
    admit_numpy(program,runtime)
    np=numpy();tiny=2.0**-149
    with np.errstate(all='ignore'):
        checks=[(1.0+2.0**-24,1.0),(1.0+3*2.0**-24,1.0+2.0**-22),
                (tiny,tiny),(tiny/2,0.0),(tiny*1.5,tiny*2),(-0.0,-0.0)]
        if np.dtype('float32').itemsize!=4 or any(word(float(np.float32(x)))!=word(y) for x,y in checks):
            raise ToolError('unsupported_arithmetic','Binary32 nearest/subnormal/signed-zero preflight failed')
    runtime['precision_profile']=program.precision['schema']
    runtime['platform']=math_platform()
    runtime['primitive_contracts']={'narrow':'binary64-to-binary32-nearest-even-gradual-subnormals',
                                    'widen':'exact-binary32-to-binary64'}
    runtime['qualification']='Selected NumPy 2.4.0 scalar conversion and CPython binary64 operations implement the declared IEEE contracts. Lean proves the model-backed storage conversions and numerical root; source mapping and runtime/compiler/hardware fidelity remain trusted.'


def python_results(program,source,cases):
    from numerics.frontends.scalar import number, word
    np=numpy();namespace={};exec(compile(source,'<admitted-mixed-storage-source>','exec'),namespace)
    fn=namespace[program.function];rows=[]
    for case in cases:
        with np.errstate(all='ignore'):value=fn(*(number(x) for x in case))
        values=value if isinstance(value,tuple) else (value,)
        if len(values)!=len(program.outputs) or any(type(x)is not float for x in values):
            raise ValueError('Mixed storage API must return the declared built-in binary64 scalars')
        rows.append(tuple(word(x) for x in values))
    return rows
