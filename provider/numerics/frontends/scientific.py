"""Closed scientific-array source admission and operation-preserving Lean model.

This is a trusted source bridge, not a proof of Python, Julia or NumPy internals.
No runtime library is needed to reparse a frozen program for Lean replay.
"""
import ast
from dataclasses import dataclass,replace
import math
import re

from numerics.graph import Graph,Scalar,Unsupported
from numerics.frontends.python_arrays import input_names, paths


@dataclass
class Tensor:
    """Symbolic storage; bound prevents alias assignment, viewed freezes writes.

    Helpers temporarily borrow owned storage; only fresh results transfer back.
    """
    dims: tuple
    items: list
    text: str
    owned: bool = True
    bound: bool = False
    viewed: bool = False


def count(dims):return math.prod(dims)


def admit(source,function,configuration,language='python',model=None):
    if not isinstance(configuration,dict) or not configuration:
        raise Unsupported('scientific_arrays maps all parameters to scalar [] or fixed rank-one/two shapes')
    if language=='julia':
        from numerics.frontends.julia_arrays import syntax
        tree=syntax(source)
    else:tree=ast.parse(source)
    functions={};imports=0
    for node in tree.body:
        if (isinstance(node,ast.Import) and len(node.names)==1 and
                node.names[0].name=='numpy' and node.names[0].asname=='np'):
            imports+=1
        elif isinstance(node,ast.FunctionDef) and node.name not in functions:functions[node.name]=node
        elif isinstance(node,ast.Expr) and isinstance(node.value,ast.Constant) and isinstance(node.value.value,str):continue
        else:raise Unsupported('Scientific source requires closed functions and exactly import numpy as np')
    if imports!=1 or function not in functions:raise Unsupported('Missing scientific entry or NumPy binding')
    reserved={'np','range','len','Float64','Vector','zeros','length'}
    if reserved & set(functions):raise Unsupported('Scientific builtins must remain unshadowed')
    arguments={}
    for name,fn in functions.items():
        a=fn.args
        if (fn.decorator_list or getattr(fn,'type_params',()) or a.vararg or a.kwarg or
                a.kwonlyargs or a.defaults or a.kw_defaults):
            raise Unsupported('Scientific functions require ordinary positional parameters')
        args=[*a.posonlyargs,*a.args]
        def annotation(node):
            return node is None or isinstance(node,ast.Name) and node.id=='float' or isinstance(node,ast.Attribute) and isinstance(node.value,ast.Name) and node.value.id=='np' and node.attr=='ndarray'
        if not annotation(fn.returns) or any(not annotation(p.annotation) for p in args):raise Unsupported('Unsupported scientific annotation')
        arguments[name]=[p.arg for p in args]
        if reserved & (set(arguments[name])|{n.id for n in ast.walk(fn) if isinstance(n,ast.Name) and isinstance(n.ctx,ast.Store)}):
            raise Unsupported('Scientific library/builtin shadowing is unsupported')
    selected=arguments[function]
    if set(selected)!=set(configuration):raise Unsupported('Scientific shapes must name every original parameter')
    if not any(configuration.values()):raise Unsupported('Scientific profile requires at least one shaped array input')
    for dims in configuration.values():
        if (not isinstance(dims,list) or len(dims)>2 or any(type(n)is not int or not 1<=n<=8 for n in dims) or count(dims)>32):
            raise Unsupported('Scientific shapes need rank 0..2, dimensions 1..8 and at most 32 cells')
    for parameter in [*functions[function].args.posonlyargs,*functions[function].args.args]:
        if parameter.annotation is not None and bool(configuration[parameter.arg]) != isinstance(parameter.annotation,ast.Attribute):
            raise Unsupported('Scientific parameter annotation disagrees with its selected shape')
        if language=='julia' and len(configuration[parameter.arg])>1:
            raise Unsupported('Julia collection profile currently uses ordinary vectors')
    names=sum((input_names(n,configuration[n]) if configuration[n] else [n] for n in selected),[])
    if len(names)>64:raise Unsupported('Scientific source admits at most 64 original cells')
    graph=Graph(language,function,names);lean=[];rendered={};offset=0;api=[]
    for i,name in enumerate(selected):
        dims=tuple(configuration[name]);values=[graph.names[n] for n in (input_names(name,dims) if dims else [name])]
        for k,value in enumerate(values):rendered[value.ref]=f'(p{i}.data.getD {k} 0.0)' if dims else f'p{i}'
        api.append((name,Tensor(dims,values,f'p{i}.data',False,True) if dims else values[0]))
        offset+=len(values)
    sequence=0;accesses=[];loops=[];active=[];env={};work=0
    def bind(text):
        nonlocal sequence
        name='v'+str(sequence);sequence+=1;lean.append('  let '+name+' := '+text);return name
    def text(value):
        if isinstance(value,Tensor):return value.text
        if isinstance(value,tuple):raise Unsupported('Tuple arithmetic is outside the scientific profile')
        return str(value.integer) if value.integer is not None else rendered[value.ref]
    def numeric(op,left,right=None):
        if not isinstance(left,Scalar) or right is not None and not isinstance(right,Scalar):
            raise Unsupported('Scientific scalar arithmetic requires binary64 or index values')
        if left.integer is not None or right is not None and right.integer is not None:
            if right is None and op in ('neg','pos') and left.integer is not None:
                return Scalar(integer=-left.integer if op=='neg' else left.integer)
            if right is not None and left.integer is not None and right.integer is not None and op in ('add','sub','mul'):
                return Scalar(integer={'add':lambda:left.integer+right.integer,'sub':lambda:left.integer-right.integer,'mul':lambda:left.integer*right.integer}[op]())
            if language!='python':raise Unsupported('Julia scientific arithmetic requires floating literals')
            def promote(v):
                if v is None or v.integer is None:return v
                if abs(v.integer)>2**53:raise Unsupported('Scientific integer promotion must be exact in binary64')
                return expr(ast.Constant(value=float(v.integer)))
            left,right=promote(left),promote(right)
        before=len(graph.nodes)
        value=graph.unary(op,left) if right is None else graph.binary(op,left,right)
        from numerics.emit.scalar import expression
        for node in graph.nodes[before:]:
            rendered[node.name]=bind(re.sub(r'\b[an]\d+\b',lambda m:rendered[m[0]],expression(node)))
        return value
    def tensor(dims,items,expression):
        if len(items)!=count(dims) or any(not isinstance(v,Scalar) or v.integer is not None for v in items):
            raise Unsupported('Collection cells must be binary64 values')
        return Tensor(tuple(dims),items,bind(expression))
    def binary(op,left,right):
        if not all(isinstance(v,(Scalar,Tensor)) for v in (left,right)):
            raise Unsupported('Scientific arithmetic does not admit tuple/container operands')
        if not isinstance(left,Tensor) and not isinstance(right,Tensor):return numeric(op,left,right)
        if language=='julia':raise Unsupported('Julia collection arithmetic needs an explicit indexed scalar loop in this profile')
        dims=left.dims if isinstance(left,Tensor) else right.dims
        if isinstance(left,Tensor) and isinstance(right,Tensor) and left.dims!=right.dims:
            raise Unsupported('Scientific broadcasting currently admits scalars or identical shapes only')
        if any(isinstance(v,Scalar) and v.integer is not None for v in [left,right]):
            def promote(v):
                if not isinstance(v,Scalar) or v.integer is None:return v
                if language!='python' or abs(v.integer)>2**53:raise Unsupported('Array integer promotion must be exact binary64')
                return expr(ast.Constant(value=float(v.integer)))
            left,right=promote(left),promote(right)
        # The scalar graph proposes numerical bounds. The separate collection
        # model retains the actual whole-array primitive and is equated in Lean.
        start=len(lean)
        items=[numeric(op,left.items[i] if isinstance(left,Tensor) else left,
                             right.items[i] if isinstance(right,Tensor) else right) for i in range(count(dims))]
        del lean[start:]
        symbol={'add':'+','sub':'-','mul':'*','div':'/'}[op]
        l=text(left) if isinstance(left,Tensor) else '#['+text(left)+']'
        r=text(right) if isinstance(right,Tensor) else '#['+text(right)+']'
        value=tensor(dims,items,f'Flare.Binary64.Collection.binary (fun a b => a {symbol} b) {count(dims)} ({l}) ({r}) '+
                     ('false' if isinstance(left,Tensor) else 'true')+' '+('false' if isinstance(right,Tensor) else 'true'))
        for i,v in enumerate(items):rendered[v.ref]=f'({value.text}.getD {i} 0.0)'
        return value
    def integer(node):
        value=expr(node)
        if not isinstance(value,Scalar) or value.integer is None:raise Unsupported('Scientific indices and extents must be fixed integers')
        return value.integer
    def location(node):
        value=expr(node.value)
        if not isinstance(value,Tensor):raise Unsupported('Indexing requires an admitted collection')
        indices=node.slice.elts if isinstance(node.slice,ast.Tuple) else [node.slice]
        if len(indices)!=len(value.dims):raise Unsupported('Scientific indexing must supply every dimension')
        at=0
        for sub,dim in zip(indices,value.dims,strict=True):
            k=integer(sub)
            if not 0<=k<dim:raise Unsupported('Scientific index is out of bounds')
            accesses.append({'line':getattr(node,'lineno',0),'index':k,'extent':dim})
            at=at*dim+k
        return value,at
    def library(node):return isinstance(node,ast.Attribute) and isinstance(node.value,ast.Name) and node.value.id=='np'
    def dtype(node):return library(node) and node.attr=='float64'
    def expr(node):
        if isinstance(node,ast.Name) and node.id in env:return env[node.id]
        if isinstance(node,ast.Constant) and type(node.value) in (float,int):
            result=graph.literal(node.value)
            if result.ref:rendered[result.ref]=bind('Float.ofBits '+str(graph.nodes[-1].bits))
            return result
        if isinstance(node,ast.Tuple):return tuple(expr(n) for n in node.elts)
        if isinstance(node,ast.Subscript):
            value,i=location(node);v=value.items[i]
            # Retain indexed source reads, rather than substituting their graph operands.
            rendered[v.ref]=bind(f'{value.text}.getD {i} 0.0');return v
        if isinstance(node,ast.Attribute) and node.attr=='T':
            value=expr(node.value)
            if not isinstance(value,Tensor) or len(value.dims)!=2:raise Unsupported('Transpose requires a rank-two collection')
            rows,cols=value.dims
            value.viewed=True
            return Tensor((cols,rows),[value.items[i*cols+j] for j in range(cols) for i in range(rows)],
                          bind(f'Flare.Binary64.Collection.transpose {rows} {cols} {value.text}'),False)
        if isinstance(node,ast.BinOp) and type(node.op) in (ast.Add,ast.Sub,ast.Mult,ast.Div):
            return binary({ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul',ast.Div:'div'}[type(node.op)],expr(node.left),expr(node.right))
        if isinstance(node,ast.UnaryOp) and type(node.op) in (ast.UAdd,ast.USub):
            value=expr(node.operand)
            if isinstance(value,Tensor):raise Unsupported('Use explicit array subtraction instead of unary collection signs')
            return numeric('neg' if isinstance(node.op,ast.USub) else 'pos',value)
        if isinstance(node,ast.Call):
            if isinstance(node.func,ast.Name) and node.func.id=='len' and len(node.args)==1 and not node.keywords:
                value=expr(node.args[0])
                if isinstance(value,Tensor):return Scalar(integer=value.dims[0])
            if isinstance(node.func,ast.Name) and node.func.id in functions and node.func.id not in env and not node.keywords:
                return call(node.func.id,[expr(n) for n in node.args])
            if library(node.func):
                op=node.func.attr
                if op in ('add','subtract','multiply','divide') and len(node.args)==2 and not node.keywords:
                    return binary({'add':'add','subtract':'sub','multiply':'mul','divide':'div'}[op],*[expr(n) for n in node.args])
                if op in ('zeros','array') and len(node.args)==1 and len(node.keywords)==1 and node.keywords[0].arg=='dtype' and dtype(node.keywords[0].value):
                    if op=='zeros':
                        dims=tuple(integer(n) for n in node.args[0].elts) if isinstance(node.args[0],ast.Tuple) else (integer(node.args[0]),)
                        if not 1<=len(dims)<=2 or any(not 1<=d<=8 for d in dims) or count(dims)>32:raise Unsupported('Unsupported allocation shape')
                        items=[expr(ast.Constant(value=0.0)) for _ in range(count(dims))]
                    else:
                        def literal(n):
                            if isinstance(n,ast.List):
                                parts=[literal(x) for x in n.elts]
                                if not parts or any(d!=parts[0][0] for d,_ in parts):raise Unsupported('Array initializer must be rectangular')
                                return (len(parts),*parts[0][0]),sum((v for _,v in parts),[])
                            return (),[expr(n)]
                        dims,items=literal(node.args[0])
                        if not 1<=len(dims)<=2 or any(not 1<=d<=8 for d in dims) or count(dims)>32:raise Unsupported('Unsupported array initializer')
                    return tensor(dims,items,'#['+', '.join(text(v) for v in items)+']')
                if op=='outer' and len(node.args)==2 and not node.keywords:
                    left,right=map(expr,node.args)
                    if not all(isinstance(v,Tensor) and len(v.dims)==1 for v in (left,right)):raise Unsupported('outer requires two vectors')
                    dims=(left.dims[0],right.dims[0])
                    if count(dims)>32:raise Unsupported('Scientific outer exceeds 32 cells')
                    start=len(lean)
                    items=[numeric('mul',a,b) for a in left.items for b in right.items];del lean[start:]
                    result=tensor(dims,items,f'Flare.Binary64.Collection.outer {dims[0]} {dims[1]} {left.text} {right.text}')
                    for i,v in enumerate(items):rendered[v.ref]=f'({result.text}.getD {i} 0.0)'
                    return result
        raise Unsupported('Unsupported scientific expression: '+type(node).__name__)
    def assign(target,value):
        if isinstance(target,ast.Name):
            if isinstance(value,Tensor):
                if value.bound:raise Unsupported('Collection alias assignment is outside this profile')
                value.bound=True
            env[target.id]=value;return
        if isinstance(target,ast.Subscript) and isinstance(value,Scalar) and value.integer is None:
            container,i=location(target)
            if not container.owned or container.viewed:raise Unsupported('Input/borrowed/view mutation is outside this profile')
            container.items[i]=value;container.text=bind(f'{container.text}.set! {i} ({text(value)})');return
        raise Unsupported('Scientific assignment requires a fresh local or owned element')
    def body(statements,in_loop=False):
        nonlocal work
        result=None
        for statement in statements:
            work+=1
            if work>10000 or len(graph.nodes)>1024:raise Unsupported('Scientific source exceeds its bounded expansion limit')
            if result is not None:raise Unsupported('Scientific statements after return are unsupported')
            if isinstance(statement,ast.Expr) and isinstance(statement.value,ast.Constant) and isinstance(statement.value.value,str):continue
            if isinstance(statement,ast.Assign) and len(statement.targets)==1:assign(statement.targets[0],expr(statement.value))
            elif isinstance(statement,ast.AugAssign) and type(statement.op) in (ast.Add,ast.Sub,ast.Mult,ast.Div):
                current=expr(statement.target)
                if isinstance(current,Tensor) and (not current.owned or current.viewed):
                    raise Unsupported('In-place updates to input/borrowed collections are outside this profile')
                assign(statement.target,binary({ast.Add:'add',ast.Sub:'sub',ast.Mult:'mul',ast.Div:'div'}[type(statement.op)],current,expr(statement.value)))
            elif isinstance(statement,ast.For) and isinstance(statement.target,ast.Name) and not statement.orelse and isinstance(statement.iter,ast.Call) and isinstance(statement.iter.func,ast.Name) and statement.iter.func.id=='range' and not statement.iter.keywords:
                bounds=[integer(n) for n in statement.iter.args]
                start,stop=(0,bounds[0]) if len(bounds)==1 else bounds if len(bounds)==2 else (0,-1)
                if not 0<=start<=stop<=32:raise Unsupported('Scientific loops need fixed nonnegative ranges at most 32')
                loops.append({'line':getattr(statement,'lineno',0),'start':start,'stop':stop})
                outer=dict(env)
                for i in range(start,stop):
                    env[statement.target.id]=Scalar(integer=i);body(statement.body,True)
                    if language=='julia':
                        for name in set(env)-set(outer):del env[name]
                        if statement.target.id in outer:env[statement.target.id]=outer[statement.target.id]
            elif isinstance(statement,ast.Return) and not in_loop:result=expr(statement.value)
            else:raise Unsupported('Unsupported scientific statement: '+type(statement).__name__)
        return result
    def call(name,values):
        nonlocal env
        if any(not isinstance(v,(Scalar,Tensor)) for v in values):raise Unsupported('Scientific helper parameters require scalar or collection values')
        if name in active or len(active)>=16 or len(values)!=len(arguments[name]):raise Unsupported('Recursive/deep/mismatched scientific helper')
        for parameter,value in zip([*functions[name].args.posonlyargs,*functions[name].args.args],values,strict=True):
            if parameter.annotation is not None and isinstance(value,Tensor)!=isinstance(parameter.annotation,ast.Attribute):
                raise Unsupported('Scientific helper argument disagrees with its declared type')
            if parameter.annotation is not None and isinstance(parameter.annotation,ast.Name) and isinstance(value,Scalar) and value.integer is not None:
                raise Unsupported('Typed Float64 helper calls require floating values')
        saved=env;env=dict(zip(arguments[name],values,strict=True));active.append(name)
        borrowed=[(v,v.owned) for v in values if isinstance(v,Tensor)]
        for v,_ in borrowed:v.owned=False
        try:
            result=body(functions[name].body)
            if result is None:raise Unsupported('Scientific functions require an explicit numeric/collection return')
            returned=list(result) if isinstance(result,tuple) else [result]
            tensors=[v for v in returned if isinstance(v,Tensor)]
            if any(not v.owned for v in tensors) or len({id(v) for v in tensors})!=len(tensors):
                raise Unsupported('Scientific returns must transfer fresh independent storage')
            for value in tensors:value.bound=False
            return result
        finally:
            for v,owned in borrowed:v.owned=owned
            active.pop();env=saved
    result=call(function,[value for _,value in api]);results=list(result) if isinstance(result,tuple) else [result]
    if not any(isinstance(v,Tensor) for v in results) or any(not isinstance(v,(Tensor,Scalar)) or isinstance(v,Tensor) and not v.owned for v in results):
        raise Unsupported('Scientific returns require fresh collection storage, optionally with scalar results')
    outputs=sum((v.items if isinstance(v,Tensor) else [v] for v in results),[])
    if len(graph.nodes)>1024:raise Unsupported('Scientific source exceeds its 1024-node bound')
    metadata={'schema':'scientific-arrays-v1','runtime':'numpy-2.4.0' if language=='python' else 'julia-1.11.7',
        'inputs':[{'name':n,'shape':configuration[n]} for n in selected],
        'outputs':[list(v.dims) if isinstance(v,Tensor) else [] for v in results],
        'accesses':accesses,'loops':loops}
    program=replace(graph.finish(outputs,32),scientific=metadata)
    if language=='python':compile(tree,'<admitted-scientific-source>','exec')
    if model is not None:
        lean.append('  #['+', '.join('⟨'+str(list(v.dims) if isinstance(v,Tensor) else [])+', '+(v.text if isinstance(v,Tensor) else '#['+text(v)+']')+'⟩' for v in results)+']')
        # Dead scalar graph intermediates are replaced by whole-array primitives.
        # Every retained let is used, or explicitly anonymous for Lean's linter.
        used='\n'.join(lean)
        lean=[re.sub(r'^(  let )(v\d+)( :=)',lambda m:m[1]+('_' if len(re.findall(r'\b'+m[2]+r'\b',used))==1 else '')+m[2]+m[3],line) for line in lean]
        model.extend(lean)
    return program
