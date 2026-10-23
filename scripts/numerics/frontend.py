"""Restricted source adapters. Each parser and runtime mapping is a trust boundary."""
import ast
from dataclasses import dataclass
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


def python_frontend(source, function, trace=None):
    tree = ast.parse(source)
    statements = [x for x in tree.body if not (
        isinstance(x, ast.Expr) and isinstance(x.value, ast.Constant)
        and isinstance(x.value.value, str))]
    if not statements or any(not isinstance(x, ast.FunctionDef) for x in statements):
        raise Unsupported('Expected numerical functions; imports and module execution are unsupported')
    functions = {fn.name: fn for fn in statements}
    if len(functions) != len(statements) or function not in functions:
        raise Unsupported('Function names must be distinct and the selected function must exist')
    if set(functions)&{'float','tuple','__builtins__'}:
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
        if isinstance(node, ast.Tuple):
            return [expression(x) for x in node.elts]
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            name = node.func.id
            if name not in functions or name in local_names[active[-1]] or node.keywords:
                raise Unsupported('Only calls to unshadowed local numerical helpers are admitted')
            args = [expression(x) for x in node.args]
            return call(name, args)
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
    return graph.finish(outputs)


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


FRONTENDS = {
    'rust': SourceAdapter(rust_frontend, None,
        'Restricted scalar f64 Rust source; parser and compiler/runtime correspondence are trusted. Optional Aeneas extraction checks the actual retained source.', ('rustc',)),
    'python': SourceAdapter(python_frontend, load_python,
        'Restricted Python scalar source, local numerical helpers, fixed literal-tuple loops, explicit ordinary scalar instance-method horizons and a separate fixed-shape built-in-list product profile; bounded AST expansion and runtime correspondence are trusted.'),
    'julia': SourceAdapter(julia_frontend, None,
        'Restricted Julia scalar source on original Float64 inputs with ordinary separate arithmetic, no fast-math or method overrides; parser, literal conversion and runtime correspondence are trusted.', ('julia',)),
    'matlab': SourceAdapter(matlab_frontend, None,
        'Restricted MATLAB-compatible scalar source on original real double inputs; parser and runtime correspondence are trusted. Octave diagnostics establish sampled Octave agreement, not MATLAB runtime agreement.', ('matlab', 'octave')),
}


def parse(language, source, function, python_method=None, python_arrays=None):
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
    env = {f'a{i}': x for i, x in enumerate(arguments)}
    for n in program.nodes:
        xs = [env[x] for x in n.args]
        if n.op == 'constant':
            value = number(n.bits)
        elif n.op == 'neg':
            value = -xs[0]
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
