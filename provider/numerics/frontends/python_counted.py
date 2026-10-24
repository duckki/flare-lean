"""Admit a real counted Python loop while retaining one scalar helper graph."""
import ast
from dataclasses import replace

from numerics.graph import Node, Unsupported


def statements(body):
    return [n for n in body if not (isinstance(n, ast.Expr) and
        isinstance(n.value, ast.Constant) and isinstance(n.value.value, str))]


def parse_counted(source, function, selection):
    from numerics.frontends.scalar import python_frontend, return_annotation
    if (not isinstance(selection, dict) or set(selection) != {'parameter','iterations'} or
            not isinstance(selection['parameter'],str) or type(selection['iterations']) is not int or
            not 0 <= selection['iterations'] <= 65536):
        raise Unsupported('python_counted needs a count parameter and 0..65536 integer iterations')
    tree = ast.parse(source)
    definitions = statements(tree.body)
    if any(not isinstance(n,ast.FunctionDef) for n in definitions):
        raise Unsupported('Counted source requires ordinary numerical function definitions')
    matches = [n for n in definitions if n.name == function]
    if len(matches) != 1 or len({n.name for n in definitions}) != len(definitions):
        raise Unsupported('Counted function names must be distinct')
    fn = matches[0]
    args = [*fn.args.posonlyargs,*fn.args.args]
    count = selection['parameter']
    if (fn.decorator_list or getattr(fn,'type_params',()) or fn.args.kwonlyargs or fn.args.vararg or
            fn.args.kwarg or fn.args.defaults or fn.args.kw_defaults or not return_annotation(fn.returns) or
            count not in [a.arg for a in args] or len({a.arg for a in args}) != len(args)):
        raise Unsupported('Counted API requires positional arguments, no defaults/decorators and a count parameter')
    for a in args:
        if a.annotation is not None and not (isinstance(a.annotation,ast.Name) and
                a.annotation.id == ('int' if a.arg == count else 'float')):
            raise Unsupported('Counted arguments must be binary64 floats and one integer count')
    names = [a.arg for a in args if a.arg != count]
    body = statements(fn.body)
    if not (len(body)==2 and isinstance(body[0],ast.For) and isinstance(body[1],ast.Return)):
        raise Unsupported('Counted profile requires one range(count) loop followed by its state return')
    loop = body[0]
    if (not isinstance(loop.target,ast.Name) or loop.target.id in [a.arg for a in args] or loop.orelse or
            not isinstance(loop.iter,ast.Call) or not isinstance(loop.iter.func,ast.Name) or
            loop.iter.func.id != 'range' or loop.iter.keywords or len(loop.iter.args)!=1 or
            not isinstance(loop.iter.args[0],ast.Name) or loop.iter.args[0].id != count or
            len(loop.body)!=1 or not isinstance(loop.body[0],ast.Assign)):
        raise Unsupported('Counted loop requires an unused index and one direct state/helper assignment')
    assignment = loop.body[0]
    if len(assignment.targets)!=1 or not isinstance(assignment.targets[0],ast.Tuple):
        raise Unsupported('Counted loop updates exactly two scalar state variables together')
    targets = assignment.targets[0].elts
    if len(targets)!=2 or any(not isinstance(n,ast.Name) for n in targets):
        raise Unsupported('Counted loop updates exactly two scalar state variables together')
    state = [n.id for n in targets]
    call = assignment.value
    if (len(set(state))!=2 or not set(state)<=set(names) or not isinstance(call,ast.Call) or
            not isinstance(call.func,ast.Name) or call.func.id in {*names,count,loop.target.id,function} or
            call.keywords or len(call.args)!=len(names) or
            any(not isinstance(n,ast.Name) for n in call.args) or
            set(n.id for n in call.args)!=set(names) or
            not isinstance(body[1].value,ast.Tuple) or
            ast.dump(body[1].value,include_attributes=False)!=ast.dump(ast.Tuple(
                elts=[ast.Name(id=n,ctx=ast.Load()) for n in state],ctx=ast.Load()),include_attributes=False)):
        raise Unsupported('Counted helper must receive original float/state variables and return the updated state')
    forbidden = {'range','float','int','tuple','__builtins__'}
    if forbidden & ({n.name for n in definitions}|{a.arg for a in args}|{loop.target.id}):
        raise Unsupported('Counted source must not shadow builtins or annotation types')
    helpers = ast.Module(body=[n for n in definitions if n is not fn],type_ignores=[])
    local = python_frontend(ast.unparse(helpers),call.func.id)
    if len(local.outputs)!=2 or len(local.inputs)!=len(names) or len(local.nodes)>64:
        raise Unsupported('Counted helper requires two outputs and at most 64 scalar nodes')
    mapping = {'a'+str(i):'a'+str(names.index(n.id)) for i,n in enumerate(call.args)}
    def ref(name):
        return mapping.get(name,name)
    compile(tree,'<admitted-counted-source>','exec')
    return replace(local,language='python',function=function,inputs=tuple(names),
        nodes=tuple(Node(n.name,n.op,tuple(ref(a) for a in n.args),n.bits) for n in local.nodes),
        outputs=tuple(ref(n) for n in local.outputs),counted={
            'schema':'python-counted-loop-v1','parameter':count,'iterations':selection['iterations'],
            'parameter_index':[a.arg for a in args].index(count),'state_slots':[names.index(n) for n in state],
            'helper':call.func.id})


def load_counted(source, program):
    from numerics.frontends.scalar import load_python
    function = load_python(source,program.function)
    def invoke(*arguments):
        args = list(arguments)
        args.insert(program.counted['parameter_index'],program.counted['iterations'])
        return function(*args)
    return invoke
