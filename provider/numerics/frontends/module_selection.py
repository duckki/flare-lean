"""Select closed original function definitions without importing an application.

Module initialization, rebinding and dispatch remain explicit caller premises.
Never execute unrelated imports or rewrite the selected operation schedule.
"""
import ast
import hashlib
from numerics.graph import Unsupported


def python_selection(source, function, *, scientific=False):
    if len(source)>2_000_000: raise Unsupported('Python module selection is limited to 2 MB')
    tree=ast.parse(source)
    definitions={n.name:n for n in tree.body if isinstance(n,ast.FunctionDef)}
    bindings={}
    class Bindings(ast.NodeVisitor):
        # Control-flow at module scope can replace a selected definition. Do not
        # confuse function/class local bindings with global module bindings.
        def bind(self,name,node):bindings.setdefault(name,[]).append(node)
        def visit_FunctionDef(self,node):self.bind(node.name,node)
        visit_AsyncFunctionDef=visit_FunctionDef
        visit_ClassDef=visit_FunctionDef
        def visit_Import(self,node):
            for item in node.names:self.bind(item.asname or item.name.split('.')[0],node)
        def visit_ImportFrom(self,node):
            for item in node.names:self.bind(item.asname or item.name,node)
        def visit_Name(self,node):
            if isinstance(node.ctx,(ast.Store,ast.Del)):self.bind(node.id,node)
    Bindings().visit(tree)
    chosen={};active=set()
    def visit(name):
        if name in active: raise Unsupported('Recursive module helper is outside the closed selection')
        if name in chosen:return
        if name not in definitions or len(bindings.get(name,[]))!=1:
            raise Unsupported('Selected function/helper is missing or rebound: '+name)
        fn=definitions[name]
        if fn.decorator_list:raise Unsupported('Selected module functions must be undecorated')
        active.add(name)
        for node in ast.walk(fn):
            if isinstance(node,ast.Call) and isinstance(node.func,ast.Name) and node.func.id in definitions:
                visit(node.func.id)
        active.remove(name);chosen[name]=fn
    visit(function)
    nodes=sorted(chosen.values(),key=lambda n:n.lineno)
    if scientific:
        imports=bindings.get('np',[])
        if (len(imports)!=1 or not isinstance(imports[0],ast.Import) or len(imports[0].names)!=1
                or imports[0].names[0].name!='numpy' or imports[0].names[0].asname!='np'):
            raise Unsupported('Selected scientific module requires an unrebound import numpy as np')
        nodes=[imports[0],*nodes]
    lines=source.splitlines(keepends=True)
    # Preserve original line numbers and bytes; only unrelated module statements
    # become blank lines. Normal frontends still reject unknown globals/calls.
    output=['\n' if line.endswith('\n') else '' for line in lines]
    for node in nodes:
        output[node.lineno-1:node.end_lineno]=lines[node.lineno-1:node.end_lineno]
    selected=''.join(output)
    return selected,{'schema':'python-closed-module-selection-v1','function':function,
        'source_sha256':hashlib.sha256(source.encode()).hexdigest(),
        'ranges':[[n.lineno,n.end_lineno] for n in nodes],
        'qualification':'Original definitions in isolation; module initialization, rebinding and dynamic dispatch are excluded and require caller review.'}


def selected_source(program,source):
    if program.selection and program.selection['schema']=='python-closed-module-selection-v1':
        selected,record=python_selection(source,program.function,scientific=program.scientific is not None)
        if record!=program.selection:raise ValueError('Original module selection changed')
        return selected
    return source
