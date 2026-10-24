"""Closed Python profile: one terminal scalar conditional over ordered arithmetic."""
import ast
import copy
from dataclasses import replace

from numerics.graph import Node, Unsupported


def parse_branches(source, function, local=False):
    from numerics.frontends.scalar import python_frontend
    tree = ast.parse(source)
    functions = [n for n in tree.body if not (isinstance(n, ast.Expr) and
        isinstance(n.value, ast.Constant) and isinstance(n.value.value, str))]
    if len(functions) != 1 or not isinstance(functions[0], ast.FunctionDef) or functions[0].name != function:
        raise Unsupported('Conditional profile requires one ordinary Python function')
    fn = functions[0]
    body = [n for n in fn.body if not (isinstance(n, ast.Expr) and
        isinstance(n.value, ast.Constant) and isinstance(n.value.value, str))]
    positions = [i for i, n in enumerate(body) if isinstance(n, ast.If)]
    if len(positions) != 1:
        raise Unsupported('Conditional profile requires one terminal if/else')
    i = positions[0]
    branch = body[i]
    if not branch.orelse and i+2 == len(body) and isinstance(body[-1], ast.Return):
        other = [body[-1]]
    elif branch.orelse and i+1 == len(body):
        other = branch.orelse
    else:
        raise Unsupported('Conditional branches must terminate the function')
    if any(not isinstance(n, (ast.Assign, ast.AnnAssign, ast.AugAssign)) for n in body[:i]):
        raise Unsupported('Conditional prefix supports direct scalar assignments')
    if any(len(nodes) != 1 or not isinstance(nodes[0], ast.Return) or
           isinstance(nodes[0].value, ast.Tuple) for nodes in [branch.body, other]):
        raise Unsupported('Each conditional arm must return one scalar expression')
    test = branch.test
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1 and
            type(test.ops[0]) in (ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
        raise Unsupported('Conditional guard requires one ordered scalar comparison')
    left, right = test.left, test.comparators[0]
    if isinstance(test.ops[0], (ast.Gt, ast.GtE)):
        left, right = right, left
    kind = 'select_lt' if isinstance(test.ops[0], (ast.Lt, ast.Gt)) else 'select_le'
    # The existing scalar frontend checks expressions, typing, local binding and
    # module forms. Four temporary outputs expose the guard and both arms.
    numeric = copy.deepcopy(tree)
    selected = next(n for n in numeric.body if isinstance(n, ast.FunctionDef))
    selected.body = copy.deepcopy(body[:i])+[ast.Return(value=ast.Tuple(
        elts=copy.deepcopy([left, right, branch.body[0].value, other[0].value]), ctx=ast.Load()))]
    ast.fix_missing_locations(numeric)
    program = python_frontend(ast.unparse(numeric), function, max_outputs=4)
    if len(program.nodes) > 32:
        raise Unsupported('Conditional profile admits at most 32 arithmetic nodes')
    name = 'n'+str(len(program.nodes))
    metadata={'schema': 'python-terminal-conditional-v1'}
    if local:
        if i != 0:
            raise Unsupported('Guard-local branches currently start with the input guard')
        refs=program.outputs[:2]; nodes={n.name:n for n in program.nodes}
        variable=next((r for r in refs if r.startswith('a')),None)
        constant=next((r for r in refs if r in nodes and nodes[r].op=='constant'),None)
        if variable is None or constant is None:
            raise Unsupported('Guard-local branches require one original float input and a float literal')
        metadata={'schema':'python-guard-local-v1','variable':variable,'constant':constant}
    compile(tree, '<admitted-conditional-source>', 'exec')
    return replace(program, nodes=(*program.nodes, Node(name, kind, program.outputs)),
                   outputs=(name,), branches=metadata)
