"""Explicit finite-horizon specialization of an ordinary scalar instance method.

The selected method AST, not a hand-written arithmetic port, is lowered. Class
construction, descriptors, subclass dispatch and arbitrary module execution are
outside this adapter. Diagnostics execute the selected original method body.
"""
import ast
import copy
from dataclasses import replace
import keyword
import math
from types import SimpleNamespace

from numerics.graph import Unsupported


def specialize(source, function, binding):
    if not isinstance(binding, dict) or set(binding) != {'state', 'constants', 'sequence'}:
        raise Unsupported('python_method requires state, constants and sequence')
    state, constants, sequence = (binding[k] for k in ('state', 'constants', 'sequence'))
    def identifier(x):
        return (isinstance(x, str) and x.isidentifier() and not keyword.iskeyword(x)
                and not x.startswith('__'))
    if (not isinstance(state, dict) or len(state) != 2 or
            not all(identifier(k) and identifier(v) for k, v in state.items()) or
            len(set(state.values())) != 2 or not isinstance(constants, dict) or
            not all(identifier(k) and type(v) is float and math.isfinite(v)
                    for k, v in constants.items()) or
            set(state) & set(constants) or not isinstance(sequence, list) or
            not 1 <= len(sequence) <= 128 or not all(identifier(x) for x in sequence) or
            len(set([*state.values(), *sequence])) != 2 + len(sequence)):
        raise Unsupported('Expected two distinct states, float constants and 1–128 distinct measurement inputs')
    parts = function.split('.')
    if len(parts) != 2:
        raise Unsupported('Method selector must be Class.method')
    classes = [n for n in ast.parse(source).body if isinstance(n, ast.ClassDef) and n.name == parts[0]]
    if len(classes) != 1 or classes[0].decorator_list or classes[0].keywords:
        raise Unsupported('Expected one undecorated ordinary class')
    cls = classes[0]
    if (any(not isinstance(b, ast.Name) or b.id != 'object' for b in cls.bases) or
            len(cls.bases) > 1 or any(
                not (isinstance(n, ast.Expr) and isinstance(n.value, ast.Constant) and
                     isinstance(n.value.value, str)) and
                not (isinstance(n, ast.FunctionDef) and not n.decorator_list and
                     n.name not in {'__getattribute__', '__getattr__', '__setattr__', '__new__'})
                for n in cls.body)):
        raise Unsupported('Custom inheritance, descriptors and attribute dispatch are unsupported')
    methods = [n for n in classes[0].body if isinstance(n, ast.FunctionDef) and n.name == parts[1]]
    if len(methods) != 1:
        raise Unsupported('Expected one selected instance method')
    original = methods[0]
    a = original.args
    names = [x.arg for x in a.args]
    if (original.decorator_list or original.returns or getattr(original, 'type_params', ())
            or a.posonlyargs or a.kwonlyargs or
            a.vararg or a.kwarg or a.kw_defaults or len(names) < 2 or names[0] != 'self' or
            any(x.annotation for x in a.args) or len(a.defaults) != len(names)-2 or
            any(not isinstance(x, ast.Constant) or x.value is not None for x in a.defaults)):
        raise Unsupported('Expected self, measurement and optional None-default scalar gains')
    try:
        compile(ast.fix_missing_locations(ast.Module(body=[copy.deepcopy(original)], type_ignores=[])),
                '<selected-instance-method>', 'exec')
    except SyntaxError as error:
        raise Unsupported('Selected method is not valid Python: '+str(error)) from error
    optional = names[2:]
    if any(n.id.startswith('attr__') for n in ast.walk(original) if isinstance(n, ast.Name)):
        raise Unsupported('Reserved attribute lowering prefix')
    for node in ast.walk(original):
        if (isinstance(node, ast.Attribute) and isinstance(node.ctx, ast.Store) and
                node.attr in constants):
            raise Unsupported('Configured constant attributes must remain immutable')
    body = copy.deepcopy(original.body)
    resolved = set()
    kept = []
    for stmt in body:
        if isinstance(stmt, ast.If):
            t = stmt.test
            if not (isinstance(t, ast.Compare) and isinstance(t.left, ast.Name) and
                    t.left.id in optional and t.left.id not in resolved and
                    len(t.ops) == 1 and isinstance(t.ops[0], ast.Is) and
                    len(t.comparators) == 1 and isinstance(t.comparators[0], ast.Constant) and
                    t.comparators[0].value is None and not stmt.orelse and len(stmt.body) == 1):
                raise Unsupported('Only leading None-default gain resolution is supported')
            assignment = stmt.body[0]
            n = t.left.id
            if not (isinstance(assignment, ast.Assign) and len(assignment.targets) == 1 and
                    isinstance(assignment.targets[0], ast.Name) and assignment.targets[0].id == n and
                    isinstance(assignment.value, ast.Attribute) and
                    isinstance(assignment.value.value, ast.Name) and assignment.value.value.id == 'self' and
                    assignment.value.attr in constants):
                raise Unsupported('Default gain must read a configured constant attribute')
            resolved.add(n)
            kept.append(assignment)
        else:
            if not (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant) and isinstance(stmt.value.value, str)) and set(optional) != resolved:
                raise Unsupported('Resolve every default before numerical execution')
            kept.append(stmt)
    if resolved != set(optional):
        raise Unsupported('Unresolved optional defaults')
    expected = list(state)
    if not (kept and isinstance(kept[-1], ast.Return) and isinstance(kept[-1].value, ast.Tuple) and
            [ast.unparse(x) for x in kept[-1].value.elts] == ['self.'+x for x in expected]):
        raise Unsupported('Method must return configured state attributes in order')

    class Lower(ast.NodeTransformer):
        def visit_Attribute(self, node):
            if not isinstance(node.value, ast.Name) or node.value.id != 'self' or not identifier(node.attr):
                raise Unsupported('Only direct ordinary self attributes are admitted')
            return ast.copy_location(ast.Name(id='attr__'+node.attr, ctx=node.ctx), node)
        def visit_Name(self, node):
            if node.id == 'self':
                raise Unsupported('Instance escape is unsupported')
            return node

    helper_args = [*( 'attr__'+x for x in state), names[1]]
    header = 'def method_step('+', '.join(helper_args)+'):\n'
    init = ''.join('    attr__'+k+' = '+repr(v)+'\n' for k, v in constants.items())
    lowered = [Lower().visit(s) for s in kept]
    helper = header + init + ''.join('    '+line+'\n' for s in lowered for line in ast.unparse(s).splitlines())
    inputs = [*state.values(), *sequence]
    wrapper = 'def method_horizon('+', '.join(inputs)+'):\n'
    wrapper += '    __flare_sx, __flare_sv = '+', '.join(state.values())+'\n'
    wrapper += '    for __flare_obs in ('+', '.join(sequence)+',):\n        __flare_sx, __flare_sv = method_step(__flare_sx, __flare_sv, __flare_obs)\n'
    wrapper += '    return __flare_sx, __flare_sv\n'
    return helper+'\n'+wrapper, original


def parse_method(source, function, binding):
    from numerics.frontends.scalar import python_frontend
    lowered, _ = specialize(source, function, binding)
    return replace(python_frontend(lowered, 'method_horizon'), function=function)


def load_method(source, function, binding):
    _, original = specialize(source, function, binding)
    module = ast.fix_missing_locations(ast.Module(body=[copy.deepcopy(original)], type_ignores=[]))
    namespace = {}
    exec(compile(module, '<original-instance-method>', 'exec'), namespace)
    method = namespace[original.name]
    def horizon(*args):
        obj = SimpleNamespace(**dict(zip(binding['state'], args[:2], strict=True)), **binding['constants'])
        for z in args[2:]:
            result = method(obj, z)
        return result
    return horizon
