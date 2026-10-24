"""Restricted source adapters. Each parser and runtime mapping is a trust boundary."""
import ast
from dataclasses import dataclass, replace
from typing import Callable

from .graph import Graph, Node, Program, Unsupported, number, word


OPERATORS = {ast.Add: 'add', ast.Sub: 'sub', ast.Mult: 'mul', ast.Div: 'div'}


def float_annotation(annotation):
    return isinstance(annotation, ast.Name) and annotation.id == 'float'


def return_annotation(annotation):
    return (annotation is None or float_annotation(annotation)
            or (isinstance(annotation, ast.Subscript)
                and isinstance(annotation.value, ast.Name) and annotation.value.id == 'tuple'
                and isinstance(annotation.slice, ast.Tuple) and len(annotation.slice.elts) == 2
                and all(float_annotation(x) for x in annotation.slice.elts)))


def python_frontend(source, function, trace=None, max_outputs=2, *, math_profile=False, mixed_profile=False):
    tree = ast.parse(source)
    statements = [x for x in tree.body if not (
        isinstance(x, ast.Expr) and isinstance(x.value, ast.Constant)
        and isinstance(x.value.value, str))]
    if mixed_profile:
        imports=[x for x in statements if isinstance(x,ast.Import)]
        if (len(imports)!=1 or len(imports[0].names)!=1 or imports[0].names[0].name!='numpy'
                or imports[0].names[0].asname!='np'):
            raise Unsupported('python_mixed requires exactly import numpy as np')
        statements=[x for x in statements if x is not imports[0]]
    if math_profile:
        imports = [x for x in statements if isinstance(x, ast.Import)]
        if len(imports) != 1 or len(imports[0].names) != 1 or imports[0].names[0].name != 'math' or imports[0].names[0].asname:
            raise Unsupported('python_math requires exactly import math without aliases')
        statements = [x for x in statements if x is not imports[0]]
    if not statements or any(not isinstance(x, ast.FunctionDef) for x in statements):
        raise Unsupported('Expected numerical functions; imports and module execution are unsupported')
    functions = {fn.name: fn for fn in statements}
    if len(functions) != len(statements) or function not in functions:
        raise Unsupported('Function names must be distinct and the selected function must exist')
    if mixed_profile and set(functions)&{'np','float','__builtins__'}:
        raise Unsupported('Mixed storage functions must not shadow numpy or scalar builtins')
    if set(functions)&({'float','tuple','__builtins__','math'} if math_profile else {'float','tuple','__builtins__'}):
        raise Unsupported('Numerical functions must not shadow annotation types or builtins')
    arguments = {}
    local_names = {}
    for fn in statements:
        if fn.decorator_list or not return_annotation(fn.returns) or getattr(fn, 'type_params', ()):
            raise Unsupported('Only undecorated numerical functions with scalar/tuple returns are admitted')
        a = fn.args
        if a.kwonlyargs or a.vararg or a.kwarg or a.defaults or a.kw_defaults:
            raise Unsupported('Only positional scalar parameters without defaults are supported')
        args = [*a.posonlyargs, *a.args]
        if len({x.arg for x in args})!=len(args):
            raise Unsupported('Numerical helper parameters must be distinct')
        if any(x.annotation is not None and not float_annotation(x.annotation) for x in args):
            raise Unsupported('Parameters must be unannotated or annotated float; inputs must be built-in binary64 values')
        arguments[fn.name] = [x.arg for x in args]
        # Python treats assigned names as local throughout the function, even
        # before the assignment. A later binding must not turn a global helper
        # call into an admitted call that actually raises UnboundLocalError.
        local_names[fn.name] = set(arguments[fn.name]) | {
            x.id for x in ast.walk(fn) if isinstance(x,ast.Name) and isinstance(x.ctx,ast.Store)}
    graph = Graph('python', function, arguments[function])
    active = []
    work = 0

    def values(node):
        if (mixed_profile and isinstance(node,ast.Call) and isinstance(node.func,ast.Name)
                and node.func.id=='float'):
            if node.keywords or len(node.args)!=1 or 'float' in local_names[active[-1]] or 'np' in local_names[active[-1]]:
                raise Unsupported('Mixed storage requires unshadowed float(np.float32(x))')
            inner=node.args[0]
            if (not isinstance(inner,ast.Call) or not isinstance(inner.func,ast.Attribute)
                    or not isinstance(inner.func.value,ast.Name) or inner.func.value.id!='np'
                    or inner.func.attr!='float32' or inner.keywords or len(inner.args)!=1):
                raise Unsupported('Mixed storage admits only paired float(np.float32(x)) conversions')
            return [graph.emit('round32',[graph.floating(expression(inner.args[0]))])]
        if math_profile and isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            if (not isinstance(node.func.value, ast.Name) or node.func.value.id != 'math'
                    or node.func.attr not in ('fma','sqrt') or 'math' in local_names[active[-1]]
                    or node.keywords or len(node.args) != (3 if node.func.attr == 'fma' else 1)):
                raise Unsupported('Only unshadowed positional math.fma(x, y, z) and math.sqrt(x) calls are admitted')
            args = [graph.floating(expression(x)) for x in node.args]
            return [graph.emit(node.func.attr, args)]
        if isinstance(node, ast.Tuple):
            return [expression(x) for x in node.elts]
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            name = node.func.id
            if name not in functions or name in local_names[active[-1]] or node.keywords:
                raise Unsupported('Only calls to unshadowed local numerical helpers are admitted')
            args = [expression(x) for x in node.args]
            return call(name, args)
        if isinstance(node, ast.Call):
            raise Unsupported('Only admitted numerical helper or explicit math.fma/math.sqrt calls are supported')
        return [expression(node)]

    def expression(node):
        if isinstance(node, ast.Name) and node.id in graph.names:
            return graph.names[node.id]
        if isinstance(node, ast.Constant):
            return graph.literal(node.value)
        if isinstance(node, ast.BinOp) and type(node.op) in OPERATORS:
            return graph.binary(OPERATORS[type(node.op)], expression(node.left), expression(node.right))
        if isinstance(node, ast.UnaryOp) and type(node.op) in (ast.USub, ast.UAdd):
            return graph.unary('neg' if isinstance(node.op, ast.USub) else 'pos', expression(node.operand))
        if isinstance(node, ast.Call):
            result = values(node)
            if len(result) == 1:
                return result[0]
            raise Unsupported('A tuple helper result needs tuple assignment or return')
        raise Unsupported(f'Unsupported numerical expression at line {getattr(node, "lineno", "?")}: {type(node).__name__}')

    def assign(target, result):
        targets = target.elts if isinstance(target, ast.Tuple) else [target]
        if any(not isinstance(x, ast.Name) for x in targets) or len(targets) != len(result):
            raise Unsupported('Only matching scalar or tuple assignments are supported')
        for name, value in zip(targets, result, strict=True):
            graph.names[name.id] = value

    def body(statements, in_loop=False):
        nonlocal work
        outputs = None
        for statement in statements:
            work += 1
            if work > 20000 or len(graph.nodes) > 10000:
                raise Unsupported('Bounded source expansion exceeds the admitted work limit')
            if isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Constant) and isinstance(statement.value.value, str):
                continue
            if outputs is not None:
                raise Unsupported('Statements after return are unsupported')
            if isinstance(statement, ast.Assign) and len(statement.targets) == 1:
                # Evaluate the complete RHS before assigning any target.
                assign(statement.targets[0], values(statement.value))
            elif (isinstance(statement, ast.AnnAssign) and isinstance(statement.target, ast.Name)
                  and float_annotation(statement.annotation) and statement.value is not None):
                assign(statement.target, values(statement.value))
            elif isinstance(statement, ast.AugAssign) and isinstance(statement.target, ast.Name) and type(statement.op) in OPERATORS:
                if statement.target.id not in graph.names:
                    raise Unsupported('Augmented assignment reads an undefined scalar')
                left = graph.names[statement.target.id]
                graph.names[statement.target.id] = graph.binary(OPERATORS[type(statement.op)], left, expression(statement.value))
            elif isinstance(statement, ast.For):
                if (not isinstance(statement.target, ast.Name) or not isinstance(statement.iter, ast.Tuple)
                        or not 1 <= len(statement.iter.elts) <= 128 or statement.orelse):
                    raise Unsupported('Only nonempty literal-tuple for loops of at most 128 elements are admitted')
                items = [expression(x) for x in statement.iter.elts]
                for item in items:
                    graph.names[statement.target.id] = item
                    body(statement.body, in_loop=True)
            elif isinstance(statement, ast.Return) and not in_loop:
                outputs = values(statement.value)
            else:
                raise Unsupported(f'Unsupported statement at line {statement.lineno}: {type(statement).__name__}')
        return outputs

    def call(name, args):
        if name in active or len(active) >= 32:
            raise Unsupported('Recursive or excessively deep numerical helper calls are unsupported')
        if len(args) != len(arguments[name]):
            raise Unsupported('Helper call arity does not match its declaration')
        saved = graph.names
        start = len(graph.nodes)
        depth = len(active)
        graph.names = dict(zip(arguments[name], args, strict=True))
        active.append(name)
        try:
            result = body(functions[name].body)
            if result is None:
                raise Unsupported('Missing numerical return')
            if trace is not None and depth and all(x.ref is not None for x in [*args, *result]):
                trace.append({'function': name, 'depth': depth, 'start': start,
                              'end': len(graph.nodes), 'inputs': tuple(x.ref for x in args),
                              'outputs': tuple(x.ref for x in result)})
            return result
        finally:
            active.pop()
            graph.names = saved

    outputs = call(function, list(graph.names.values()))
    # The last return expression can emit nodes after the statement-entry check.
    if len(graph.nodes) > 10000:
        raise Unsupported('Bounded source expansion exceeds the admitted work limit')
    compile(tree,'<admitted-numerical-source>','exec')
    program = graph.finish(outputs, max_outputs=max_outputs)
    if math_profile:
        operations = sorted({n.op for n in program.nodes} & {'fma','sqrt'})
        if not operations or len(program.nodes) > 32:
            raise Unsupported('python_math requires an admitted math primitive and at most 32 IR nodes')
        schema = 'python-math-sqrt-v1' if 'sqrt' in operations else 'python-math-fma-v1'
        program = replace(program, math={'schema':schema,'operations':operations})
    if mixed_profile:
        if not any(n.op=='round32' for n in program.nodes) or len(program.nodes)>32:
            raise Unsupported('python_mixed requires binary32 storage and at most 32 IR nodes')
        program=replace(program,precision={'schema':'python-numpy-storage32-v1',
            'storage':'binary32','computation':'binary64','conversion':'narrow-nearest-even-exact-widen'})
    return program


@dataclass(frozen=True)
class SourceAdapter:
    parse: Callable
    load_for_diagnostics: Callable | None
    assurance: str
    runtimes: tuple = ()


def load_python(source, function):
    namespace = {}
    # Call only after the module forms and selected call graph are admitted.
    exec(compile(source, '<admitted-numerical-source>', 'exec'), namespace)
    return namespace[function]


def julia_frontend(source, function):
    from .scalar_languages import scalar_frontend
    return scalar_frontend('julia', source, function)


def matlab_frontend(source, function):
    from .scalar_languages import scalar_frontend
    return scalar_frontend('matlab', source, function)


def rust_frontend(source, function):
    from .rust_frontend import rust_frontend as parse_rust
    return parse_rust(source, function)


def c_frontend(source, function):
    from .c_frontend import c_frontend as admit_c
    return admit_c(source, function)


FRONTENDS = {
    'cpp': SourceAdapter(None, None,
        'Closed C++20 namespace-level by-value double functions. The source selector, C syntax bridge, standard header constants and compiler/runtime fidelity are trusted. No object, memory, template, exception or standard-library algorithm coverage.', ('clang++','g++')),
    'c': SourceAdapter(c_frontend, None,
        'Closed C11 double profile with pure scalar helpers, double-only value structs, static buffers and bounded unsigned loops. Parsing/source-to-heap mapping and compiler/runtime fidelity are trusted; Lean checks abstract memory safety and numerical contracts.', ('clang','gcc')),
    'rust': SourceAdapter(rust_frontend, None,
        'Restricted scalar f64 Rust source; parser and compiler/runtime correspondence are trusted. Optional Aeneas extraction checks the actual retained source.', ('rustc',)),
    'python': SourceAdapter(python_frontend, load_python,
        'Restricted Python scalar source, local numerical helpers, fixed literal-tuple loops, explicit ordinary scalar instance-method horizons, fixed-shape built-in-list products, explicit math.fma/math.sqrt, explicit NumPy binary32 storage round trips, terminal conditionals and compact two-state counted loops; frontend/model generation and runtime correspondence are trusted.'),
    'julia': SourceAdapter(julia_frontend, None,
        'Restricted Julia scalar source on original Float64 inputs with ordinary separate arithmetic, no fast-math or method overrides; parser, literal conversion and runtime correspondence are trusted.', ('julia',)),
    'matlab': SourceAdapter(matlab_frontend, None,
        'Restricted MATLAB-compatible scalar source on original real double inputs; parser and runtime correspondence are trusted. Octave diagnostics establish sampled Octave agreement, not MATLAB runtime agreement.', ('matlab', 'octave')),
}


def parse(language, source, function, python_method=None, python_arrays=None, python_branches=None, python_counted=None, scientific_arrays=None, python_math=None, python_mixed=None, python_module=None, cpp_module=None):
    if cpp_module is not None:
        if language!='cpp' or any(x is not None for x in (python_method,python_arrays,python_branches,python_counted,scientific_arrays,python_math,python_mixed,python_module)):
            raise Unsupported('cpp_module uses its own closed C++ scalar profile')
        from .cpp_frontend import admit
        return admit(source,function,cpp_module)
    if language=='cpp':raise Unsupported('C++ source requires an explicit cpp_module selection')
    if python_module is not None:
        if python_module is not True or language!='python' or any(x is not None for x in (python_method,python_arrays,python_branches,python_counted,python_math,python_mixed)):
            raise Unsupported('python_module requires true on the scalar or scientific Python profile')
        from .module_selection import python_selection
        selected,record=python_selection(source,function,scientific=scientific_arrays is not None)
        program=parse(language,selected,function,scientific_arrays=scientific_arrays)
        return replace(program,selection=record)
    if python_mixed is not None:
        if (python_mixed is not True or language!='python' or any(x is not None for x in
                (python_method,python_arrays,python_branches,python_counted,scientific_arrays,python_math))):
            raise Unsupported('python_mixed requires true on its own ordinary Python scalar profile')
        return python_frontend(source,function,mixed_profile=True)
    if python_math is not None:
        if (python_math is not True or language != 'python' or any(x is not None for x in
                (python_method,python_arrays,python_branches,python_counted,scientific_arrays))):
            raise Unsupported('python_math requires true on its own ordinary Python scalar profile')
        return python_frontend(source,function,math_profile=True)
    if scientific_arrays is not None:
        if language not in ('python','julia') or any(x is not None for x in (python_method,python_arrays,python_branches,python_counted)):
            raise Unsupported('scientific_arrays uses its own Python/Julia source profile')
        from .scientific import admit
        return admit(source,function,scientific_arrays,language)
    if python_counted is not None:
        if language != 'python' or any(x is not None for x in [python_method,python_arrays,python_branches]):
            raise Unsupported('python_counted requires an ordinary Python function and its own source profile')
        from .python_counted import parse_counted
        return parse_counted(source,function,python_counted)
    if python_branches is not None:
        local=type(python_branches) is dict and python_branches=={'domains':'guard'}
        if (python_branches is not True and not local) or language != "python" or python_method is not None or python_arrays is not None:
            raise Unsupported("python_branches requires true or {domains: guard} on an ordinary Python scalar function")
        from .python_branches import parse_branches
        return parse_branches(source, function,local)
    if python_arrays is not None:
        if language != 'python' or python_method is not None:
            raise Unsupported('python_arrays requires ordinary Python functions')
        from .python_arrays import parse_arrays
        return parse_arrays(source,function,python_arrays)
    if python_method is not None:
        if language != "python":
            raise Unsupported("python_method requires the Python frontend")
        from .python_method import parse_method
        return parse_method(source, function, python_method)
    if language not in FRONTENDS:
        raise Unsupported(f'No admitted frontend for {language}; available: {", ".join(FRONTENDS)}')
    return FRONTENDS[language].parse(source, function)


def execute(program, arguments):
    """Independent diagnostic interpreter; it does not establish the certificate."""
    if program.counted:
        from .counted import local_program
        local=local_program(program); values=list(arguments)
        slots=program.counted['state_slots']
        for _ in range(program.counted['iterations']):
            result=execute(local,values)
            for slot,value in zip(slots,result,strict=True):
                values[slot]=value
        return tuple(values[slot] for slot in slots)
    if program.branches and program.branches['schema']=='python-guard-local-v1':
        from .branch_local import execute_local
        return execute_local(program,arguments)
    env = {f'a{i}': x for i, x in enumerate(arguments)}
    for n in program.nodes:
        xs = [env[x] for x in n.args]
        if n.op == 'constant':
            value = number(n.bits)
        elif n.op == 'neg':
            value = -xs[0]
        elif n.op in ('select_lt', 'select_le'):
            value = xs[2] if (xs[0] < xs[1] if n.op == 'select_lt' else xs[0] <= xs[1]) else xs[3]
        elif n.op=='round32':
            import struct
            value=struct.unpack('>f',struct.pack('>f',xs[0]))[0]
        elif n.op in ('fma','sqrt'):
            import math
            value = getattr(math,n.op)(*xs)
        elif n.op == 'add':
            value = xs[0] + xs[1]
        elif n.op == 'sub':
            value = xs[0] - xs[1]
        elif n.op == 'mul':
            value = xs[0] * xs[1]
        else:
            value = xs[0] / xs[1]
        env[n.name] = value
    return tuple(env[x] for x in program.outputs)
