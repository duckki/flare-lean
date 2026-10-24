"""Fixed-shape built-in lists: checked indexing, fresh storage and ordered products.

This is a trusted, deliberately closed source adapter, not a Python compiler proof.
It emits both the scalar graph and a persistent-array model from the admitted AST.
"""
import ast
from dataclasses import dataclass, replace
import itertools
import re

from numerics.graph import Graph, Scalar, Unsupported
from numerics.frontends.scalar import OPERATORS


@dataclass
class Array:
    items: list
    expression: str
    owned: bool = False
    bound: bool = False


def shape(value):
    if not isinstance(value, Array):
        return []
    shapes = [shape(x) for x in value.items]
    if not shapes or any(x != shapes[0] for x in shapes):
        raise Unsupported('Arrays must have a nonempty rectangular shape')
    return [len(shapes), *shapes[0]]


def leaves(value):
    return list(itertools.chain.from_iterable(leaves(x) for x in value.items)) if isinstance(value, Array) else [value]


def paths(dimensions):
    return itertools.product(*(range(n) for n in dimensions))


def input_names(name, dimensions):
    return [name + '_' + '_'.join(map(str, index)) for index in paths(dimensions)]


def access(name, indices):
    for i, index in enumerate(indices):
        name = f'({name}.getD {index} ' + ('#[])' if i + 1 < len(indices) else '0.0)')
    return name


def parse_arrays(source, function, configuration, model=None):
    if not isinstance(configuration, dict) or not configuration:
        raise Unsupported('python_arrays must map every input parameter to a fixed list shape')
    tree = ast.parse(source)
    statements = [x for x in tree.body if not (isinstance(x, ast.Expr) and
        isinstance(x.value, ast.Constant) and isinstance(x.value.value, str))]
    if any(not isinstance(x, ast.FunctionDef) for x in statements):
        raise Unsupported('Array source admits function definitions only')
    functions = {fn.name: fn for fn in statements}
    if len(functions) != len(statements) or function not in functions or set(functions) & {'range','len','float','list','__builtins__'}:
        raise Unsupported('Expected distinct, unshadowed numerical function names')
    arguments, locals_ = {}, {}
    def annotation(node):
        return (node is None or isinstance(node,ast.Name) and node.id=='float' or
                isinstance(node,ast.Subscript) and isinstance(node.value,ast.Name) and
                node.value.id=='list' and annotation(node.slice))
    for fn in statements:
        a = fn.args
        if (fn.decorator_list or getattr(fn, 'type_params', ()) or a.vararg or a.kwarg or
                a.kwonlyargs or a.defaults or a.kw_defaults):
            raise Unsupported('Array functions require ordinary positional parameters without defaults')
        args = [*a.posonlyargs, *a.args]
        if not annotation(fn.returns) or any(not annotation(x.annotation) for x in args):
            raise Unsupported('Only built-in float/list annotations are admitted')
        arguments[fn.name] = [x.arg for x in args]
        locals_[fn.name] = set(arguments[fn.name]) | {n.id for n in ast.walk(fn)
            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)}
    selected = arguments[function]
    if set(selected) != set(configuration) or len(selected) != 2:
        raise Unsupported('The array product profile requires exactly two shaped input parameters')
    shapes = [configuration[name] for name in selected]
    if any(not isinstance(s, list) or not 1 <= len(s) <= 2 or
           any(type(n) is not int or not 1 <= n <= 8 for n in s) for s in shapes):
        raise Unsupported('Array dimensions must be explicit integers from 1 through 8, rank one or two')
    if len(shapes[0]) != 2 or shapes[0][1] != shapes[1][0]:
        raise Unsupported('Product shapes require a rows-by-inner matrix and matching right operand')
    rows, inner = shapes[0]; columns = shapes[1][1] if len(shapes[1]) == 2 else 1
    if rows * columns > 32:
        raise Unsupported('Array product output exceeds 32 entries')
    names = sum((input_names(name, dims) for name, dims in zip(selected, shapes, strict=True)), [])
    graph = Graph('python', function, names)
    lean = []
    scalar_expr = {f'a{i}':access('p'+str(p), index) for p, dims in enumerate(shapes)
                   for i, index in enumerate(paths(dims), start=sum(len(input_names(selected[q], shapes[q])) for q in range(p)))}
    counter = 0
    def bind(expression):
        nonlocal counter
        name = 'v'+str(counter); counter += 1
        lean.append(f'  let {name} := {expression}')
        return name
    def array(items):
        if any(isinstance(item,Scalar) and item.integer is not None for item in items):
            raise Unsupported('Array storage requires float literals and binary64 values')
        result = Array(items, bind('#['+', '.join(render(x) for x in items)+']'), True)
        shape(result)
        if len(shape(result)) > 2:
            raise Unsupported('Nested arrays beyond rank two are unsupported')
        for item in items:
            if isinstance(item, Array):
                if item.bound or not item.owned:
                    raise Unsupported('Aliased or borrowed matrix rows are unsupported')
                item.bound = True
        return result
    def render(value):
        if isinstance(value, Array): return value.expression
        if value.integer is not None: return f'({value.integer} : Nat)'
        return scalar_expr[value.ref]
    def numerical(op, a, b=None):
        if isinstance(a, Array) or isinstance(b, Array):
            raise Unsupported('Use explicit indexed scalar arithmetic for array operations')
        if b is not None and a.integer is not None and b.integer is not None:
            if op not in ('add','sub','mul'):
                raise Unsupported('Integer division is outside the array profile')
            return Scalar(integer={'add':lambda:a.integer+b.integer,'sub':lambda:a.integer-b.integer,
                                   'mul':lambda:a.integer*b.integer}[op]())
        result = graph.unary(op,a) if b is None else graph.binary(op,a,b)
        # Promotions can emit constants before the operation itself.
        from numerics.emit.scalar import expression
        for node in graph.nodes:
            if node.name not in scalar_expr:
                text = expression(node)
                text = re.sub(r'\b[an]\d+\b', lambda m:scalar_expr[m[0]], text)
                scalar_expr[node.name] = bind(text)
        return result
    active = []
    environment = {}
    work = 0
    def index(node, array_value):
        value = expression(node)
        if not isinstance(value, Scalar) or value.integer is None or not 0 <= value.integer < len(array_value.items):
            raise Unsupported('Array indices must be statically in bounds; negative and dynamic indices are unsupported')
        return value.integer
    def builtin(node, name):
        return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and
                node.func.id == name and name not in locals_[active[-1]] and not node.keywords)
    def expression(node):
        if isinstance(node, ast.Name) and node.id in environment:
            return environment[node.id]
        if isinstance(node, ast.Constant):
            result = graph.literal(node.value)
            if result.ref: scalar_expr[result.ref] = bind(f'Float.ofBits {graph.nodes[-1].bits}')
            return result
        if isinstance(node, ast.List): return array([expression(x) for x in node.elts])
        if isinstance(node, ast.Subscript):
            value = expression(node.value)
            if not isinstance(value, Array): raise Unsupported('Only array indexing is supported')
            return value.items[index(node.slice, value)]
        if builtin(node,'len') and len(node.args) == 1:
            value = expression(node.args[0])
            if isinstance(value, Array): return Scalar(integer=len(value.items))
        if isinstance(node, ast.UnaryOp) and type(node.op) in (ast.USub, ast.UAdd):
            return numerical('neg' if isinstance(node.op, ast.USub) else 'pos',expression(node.operand))
        if isinstance(node, ast.BinOp) and type(node.op) in OPERATORS:
            left, right = expression(node.left), expression(node.right)
            if isinstance(node.op, ast.Mult) and isinstance(left, Array):
                if (not isinstance(right, Scalar) or right.integer is None or not 1 <= right.integer <= 32
                        or any(isinstance(x,Array) for x in left.items)):
                    raise Unsupported('Repeated matrix rows alias; only scalar-list repetition is admitted')
                return array(left.items * right.integer)
            return numerical(OPERATORS[type(node.op)],left,right)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            name = node.func.id
            if name not in functions or name in locals_[active[-1]] or node.keywords:
                raise Unsupported('Only unshadowed local array helpers, len and fixed range are admitted')
            return call(name,[expression(x) for x in node.args])
        raise Unsupported('Unsupported array expression: '+type(node).__name__)
    def assign(target, value):
        if isinstance(target, ast.Name):
            if isinstance(value, Array):
                if value.bound or not value.owned:
                    raise Unsupported('Array alias assignment and input mutation are unsupported; allocate fresh output storage')
                value.bound = True
            environment[target.id] = value
            return
        if not isinstance(target, ast.Subscript) or isinstance(value, Array):
            raise Unsupported('Only scalar element updates to fresh arrays are admitted')
        chain = []
        node = target
        while isinstance(node, ast.Subscript): chain.append(node.slice);node = node.value
        if not isinstance(node, ast.Name) or node.id not in environment:
            raise Unsupported('Element updates need a named fresh array')
        current = environment[node.id]; parents = []
        for sub in reversed(chain):
            if not isinstance(current,Array) or not current.owned:
                raise Unsupported('Input arrays and borrowed rows are read-only')
            at = index(sub,current);parents.append((current,at));current = current.items[at]
        for container, at in reversed(parents):
            container.items[at] = value
            container.expression = bind(f'{container.expression}.set! {at} {render(value)}')
            value = container
    def body(statements, in_loop=False):
        nonlocal work
        returned = None
        for statement in statements:
            work += 1
            if work > 20000 or len(graph.nodes)>10000: raise Unsupported('Array expansion exceeds its work limit')
            if returned is not None: raise Unsupported('Statements after return are unsupported')
            if isinstance(statement, ast.Expr) and isinstance(statement.value, ast.Constant) and isinstance(statement.value.value,str): continue
            if isinstance(statement, ast.Assign) and len(statement.targets)==1:
                assign(statement.targets[0],expression(statement.value))
            elif isinstance(statement, ast.AnnAssign) and statement.value is not None:
                assign(statement.target,expression(statement.value))
            elif isinstance(statement, ast.AugAssign) and type(statement.op) in OPERATORS:
                assign(statement.target,numerical(OPERATORS[type(statement.op)],expression(statement.target),expression(statement.value)))
            elif isinstance(statement, ast.For) and isinstance(statement.target, ast.Name) and not statement.orelse and builtin(statement.iter,'range'):
                values = [expression(x) for x in statement.iter.args]
                if len(values)!=1 or values[0].integer is None or not 0<=values[0].integer<=32:
                    raise Unsupported('Array loops require range(fixed_size), at most 32 iterations')
                for k in range(values[0].integer):
                    environment[statement.target.id] = Scalar(integer=k)
                    body(statement.body,True)
            elif isinstance(statement, ast.Assert) and statement.msg is None:
                test=statement.test
                if (not isinstance(test,ast.Compare) or len(test.ops)!=1 or not isinstance(test.ops[0],ast.Eq)
                        or not builtin(test.left,'len') or len(test.comparators)!=1):
                    raise Unsupported('Only fixed len(array) == size assertions are admitted')
                left,right=expression(test.left),expression(test.comparators[0])
                if left.integer is None or right.integer is None or left.integer!=right.integer:
                    raise Unsupported('Source shape assertion disagrees with the requested input shape')
            elif isinstance(statement,ast.Return) and not in_loop:
                returned=expression(statement.value)
            else: raise Unsupported('Unsupported array statement: '+type(statement).__name__)
        return returned
    def call(name,args):
        nonlocal environment
        if name in active or len(active)>=16 or len(args)!=len(arguments[name]):
            raise Unsupported('Recursive, deep or mismatched array helper call')
        saved=environment;environment=dict(zip(arguments[name],args,strict=True));active.append(name)
        # Helpers may read but never mutate their array arguments.
        borrowed=[];seen=set()
        def borrow(value):
            if isinstance(value,Array) and id(value) not in seen:
                seen.add(id(value))
                borrowed.append((value,value.owned));value.owned=False
                for child in value.items: borrow(child)
        for value in args: borrow(value)
        try:
            result=body(functions[name].body)
            if result is None or isinstance(result,Array) and not result.owned:
                raise Unsupported('Array returns must use fresh storage')
            if isinstance(result,Array): result.bound=False
            return result
        finally:
            for value,owned in borrowed: value.owned=owned
            active.pop();environment=saved
    offset=0; input_values=[]
    for p,dims in enumerate(shapes):
        values=iter(Scalar(ref='a'+str(i)) for i in range(offset,offset+len(input_names(selected[p],dims))))
        def build(ds, prefix=()):
            items=[build(ds[1:],(*prefix,i)) if len(ds)>1 else next(values) for i in range(ds[0])]
            text='p'+str(p)
            for at in prefix: text=f'({text}.getD {at} #[])'
            return Array(items,text,False,True)
        input_values.append(build(dims));offset+=len(input_names(selected[p],dims))
    result=call(function,input_values)
    if not isinstance(result,Array): raise Unsupported('Selected array function must return fresh array storage')
    expected_shape=[rows,columns] if len(shapes[1])==2 else [rows]
    if shape(result)!=expected_shape: raise Unsupported('Returned array shape does not match the ordered matrix product')
    program=graph.finish(leaves(result),32)
    metadata={'inputs':[{'name':name,'shape':dims} for name,dims in zip(selected,shapes,strict=True)],
              'output_shape':expected_shape,'product':[rows,inner,columns]}
    program=replace(program,arrays=metadata)
    validate_product(program)
    if model is not None:
        lines=[*lean,'  '+result.expression]
        uses='\n'.join(lines)
        lines=[re.sub(r'^(  let )(v\d+)( :=)',
            lambda m:m[1]+('_' if len(re.findall(r'\b'+m[2]+r'\b',uses))==1 else '')+m[2]+m[3],line)
            for line in lines]
        model.extend(lines)
    compile(tree,'<admitted-array-source>','exec')
    return program


def validate_product(program):
    """Require the exact native schedule, including the initial +0 and every add."""
    nodes={node.name:node for node in program.nodes}
    def tree(ref):
        if ref.startswith('a'): return ref
        node=nodes[ref]
        return (node.op,node.bits) if node.op=='constant' else (node.op,*map(tree,node.args))
    rows,inner,columns=program.arrays['product'];right=rows*inner
    expected=[]
    for i in range(rows):
        for j in range(columns):
            value=('constant',0)
            for k in range(inner):
                value=('add',value,('mul',f'a{i*inner+k}',f'a{right+k*columns+j}'))
            expected.append(value)
    if list(map(tree,program.outputs))!=expected:
        raise Unsupported('Array profile requires the ascending, separately rounded matrix-product schedule starting at +0.0')


def load_arrays(source,function,metadata):
    from numerics.frontends.scalar import load_python
    original=load_python(source,function)
    def invoke(*scalars):
        values=iter(scalars)
        def build(dims):
            return [build(dims[1:]) if len(dims)>1 else next(values) for _ in range(dims[0])]
        inputs=[build(field['shape']) for field in metadata['inputs']]
        result=original(*inputs)
        def flatten(value,dims):
            if type(value) is not list or len(value)!=dims[0]:
                raise ValueError('Original Python returned the wrong array shape')
            return sum((flatten(x,dims[1:]) for x in value),[]) if len(dims)>1 else value
        return tuple(flatten(result,metadata['output_shape']))
    return invoke
