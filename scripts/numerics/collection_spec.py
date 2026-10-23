"""Independent exact collection algebra on original inputs; no source execution."""
import ast
from dataclasses import dataclass
from fractions import Fraction as Q

from .scientific import count


@dataclass
class Value:
    dims: tuple
    cells: list


def specification(request,program):
    if not isinstance(request,dict) or set(request)!={'kind','bindings','outputs'} or request['kind']!='collections':
        raise ValueError('Scientific references require collections, bindings and outputs')
    if not isinstance(request['bindings'],list) or not isinstance(request['outputs'],list):raise ValueError('Collection bindings/outputs must be lists')
    from .emit import real,returned
    names={};offset=0;lines=[];expression_source=None
    for field in program.scientific['inputs']:
        dims=tuple(field['shape']);names[field['name']]=Value(dims,['a'+str(offset+i) for i in range(count(dims))]);offset+=count(dims)
    def visit(node):
        if isinstance(node,ast.Name) and node.id in names:return names[node.id]
        if isinstance(node,ast.Constant) and type(node.value) in (float,int):return Value((),[real(Q(ast.get_source_segment(expression_source,node)))])
        if isinstance(node,ast.List):
            parts=[visit(n) for n in node.elts]
            if not parts or any(v.dims!=parts[0].dims for v in parts):raise ValueError('Exact collection literal must be rectangular')
            return Value((len(parts),*parts[0].dims),sum((v.cells for v in parts),[]))
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):
            v=visit(node.operand);return Value(v.dims,['(-'+c+')' for c in v.cells])
        if isinstance(node,ast.Attribute) and node.attr=='T':
            v=visit(node.value)
            if len(v.dims)!=2:raise ValueError('Exact transpose requires a matrix')
            rows,cols=v.dims;return Value((cols,rows),[v.cells[i*cols+j] for j in range(cols) for i in range(rows)])
        if isinstance(node,ast.BinOp):
            a,b=visit(node.left),visit(node.right)
            if isinstance(node.op,ast.MatMult):
                if not a.dims or not b.dims or a.dims[-1]!=b.dims[0]:raise ValueError('Exact product has incompatible shapes')
                rows=a.dims[0] if len(a.dims)==2 else 1;inner=a.dims[-1];cols=b.dims[1] if len(b.dims)==2 else 1
                dims=(*(a.dims[:1] if len(a.dims)==2 else ()),*(b.dims[1:] if len(b.dims)==2 else ()))
                left='!!['+'; '.join(', '.join(a.cells[i*inner+k] for k in range(inner)) for i in range(rows))+']'
                right='!!['+'; '.join(', '.join(b.cells[k*cols+j] for j in range(cols)) for k in range(inner))+']'
                cells=[f'(({left}) * ({right})) ⟨{i}, by decide⟩ ⟨{j}, by decide⟩' for i in range(rows) for j in range(cols)]
                return Value(dims,cells)
            if type(node.op) not in (ast.Add,ast.Sub,ast.Mult,ast.Div):raise ValueError('Unsupported exact collection arithmetic')
            if a.dims and b.dims and a.dims!=b.dims:raise ValueError('Exact collection broadcasting requires scalars or equal shapes')
            dims=a.dims or b.dims;op={ast.Add:'+',ast.Sub:'-',ast.Mult:'*',ast.Div:'/'}[type(node.op)]
            return Value(dims,['('+a.cells[i if a.dims else 0]+' '+op+' '+b.cells[i if b.dims else 0]+')' for i in range(count(dims))])
        if isinstance(node,ast.Call) and isinstance(node.func,ast.Name) and node.func.id=='outer' and len(node.args)==2 and not node.keywords:
            a,b=map(visit,node.args)
            if len(a.dims)!=1 or len(b.dims)!=1:raise ValueError('Exact outer requires vectors')
            return Value((a.dims[0],b.dims[0]),['('+x+' * '+y+')' for x in a.cells for y in b.cells])
        raise ValueError('Unsupported exact collection expression '+type(node).__name__)
    def parse(source):
        nonlocal expression_source
        expression_source=source
        return visit(ast.parse(source,mode='eval').body)
    for i,binding in enumerate(request['bindings']):
        if not isinstance(binding,list) or len(binding)!=2 or not all(isinstance(s,str) for s in binding):raise ValueError('Exact binding is [name, expression]')
        name,expression=binding
        if not name.isidentifier() or name in names:raise ValueError('Exact binding must use a fresh name')
        value=parse(expression)
        for j,cell in enumerate(value.cells):lines.append(f'let b{i}_{j} : ℝ := {cell}')
        names[name]=Value(value.dims,[f'b{i}_{j}' for j in range(len(value.cells))])
    values=[parse(expression) for expression in request['outputs']]
    if [list(v.dims) for v in values]!=program.scientific['outputs']:raise ValueError('Exact return shapes disagree with the original API')
    lines.append(returned(sum((v.cells for v in values),[])))
    return lines
