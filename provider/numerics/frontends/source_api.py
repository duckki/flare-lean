"""Lower an ordinary scalar constructor and full-state update to a Lean model.

The mapping is a declared Python frontend trust boundary. It preserves every
field and None-default option; it never executes unrelated module/class code.
"""
import ast
import math
import re

from numerics.graph import Unsupported, word


def identifier(name):
    if not isinstance(name, str) or not re.fullmatch(r'[A-Za-z][A-Za-z_0-9]*', name):
        raise Unsupported('Expected an ordinary scalar API identifier')
    return name


def lower(source, function, rust_type):
    """Return model source and its scalar API description, derived from the AST."""
    from numerics.frontends.python_method import specialize
    cls_name, method_name = function.split('.')
    # Reuse the ordinary-class rejection rules before admitting construction.
    tree = ast.parse(source)
    classes = [n for n in tree.body if isinstance(n, ast.ClassDef) and n.name == cls_name]
    if len(classes) != 1:
        raise Unsupported('Expected one scalar API class')
    cls = classes[0]
    methods = {n.name: n for n in cls.body if isinstance(n, ast.FunctionDef)}
    if '__init__' not in methods or method_name not in methods:
        raise Unsupported('Scalar API needs a constructor and selected method')
    constructor, method = methods['__init__'], methods[method_name]
    args = constructor.args
    parameters = [identifier(n.arg) for n in args.args[1:]]
    if (not args.args or args.args[0].arg != 'self' or args.defaults or args.posonlyargs or
            args.kwonlyargs or args.kw_defaults or args.vararg or args.kwarg or
            constructor.decorator_list or constructor.returns or
            any(n.annotation for n in args.args) or getattr(constructor, 'type_params', ())):
        raise Unsupported('Expected self and required scalar constructor arguments')
    if not re.fullmatch(r'Workflow\.Generated(?:\.[A-Za-z_][A-Za-z_0-9]*)+', rust_type):
        raise Unsupported('Invalid extracted Rust API type')
    fields, initial = [], {}
    assumptions = []
    divisors = []

    def expression(node, values, locals_):
        if isinstance(node, ast.Name) and node.id in locals_:
            return locals_[node.id]
        if (isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and
                node.value.id == 'self' and node.attr in values):
            return values[node.attr]
        if isinstance(node, ast.Constant) and type(node.value) in (int, float):
            # Constructor constants must already denote scalar binary64 words.
            if type(node.value) is int and abs(node.value) > 2**53:
                raise Unsupported('Inexact scalar API integer promotion')
            if not math.isfinite(float(node.value)):
                raise Unsupported('Expected finite scalar API constants')
            return '(Float.ofBits '+str(word(float(node.value)))+')'
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return '(Float.neg '+expression(node.operand, values, locals_)+')'
        if isinstance(node, ast.BinOp) and type(node.op) in (ast.Add, ast.Sub, ast.Mult, ast.Div):
            op = {ast.Add:'add', ast.Sub:'sub', ast.Mult:'mul', ast.Div:'div'}[type(node.op)]
            a, b = expression(node.left, values, locals_), expression(node.right, values, locals_)
            if op == 'div':
                divisors.append(b)
            return '(Float.'+op+' '+a+' '+b+')'
        raise Unsupported('Unsupported scalar API expression: '+ast.dump(node, include_attributes=False))

    def assignment(node, values, locals_, declarations):
        if not isinstance(node, ast.Assign) or len(node.targets) != 1:
            raise Unsupported('Expected a direct scalar API assignment')
        target = node.targets[0]
        value = expression(node.value, values, locals_)
        name = 'f'+str(len(declarations))
        declarations.append((name, value))
        if isinstance(target, ast.Attribute) and isinstance(target.value, ast.Name) and target.value.id == 'self':
            attribute = identifier(target.attr)
            if attribute not in fields:
                if values is not initial:
                    raise Unsupported('Update writes a field not initialized by the constructor')
                fields.append(attribute)
            values[attribute] = name
        elif isinstance(target, ast.Name):
            locals_[identifier(target.id)] = name
        else:
            raise Unsupported('Only ordinary self fields and scalar locals are admitted')

    def docstring(node):
        return isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant) and isinstance(node.value.value, str)

    if any(isinstance(n, ast.BinOp) for n in ast.walk(constructor)):
        raise Unsupported('Constructor arithmetic needs a separate numerical admission rule')
    init_declarations = []
    locals_ = {name: name for name in parameters}
    for node in constructor.body:
        if docstring(node):
            continue
        if isinstance(node, ast.If):
            # An explicit scalar specialization, not a NumPy array bridge.
            t = node.test
            if not (isinstance(t, ast.Compare) and len(t.ops) == 1 and isinstance(t.ops[0], ast.Eq)
                    and isinstance(t.comparators[0], ast.Constant) and t.comparators[0].value == 0
                    and isinstance(t.left, ast.Call) and len(t.left.args) == 1 and not t.left.keywords
                    and isinstance(t.left.func, ast.Attribute) and t.left.func.attr == 'ndim'
                    and isinstance(t.left.func.value, ast.Name)
                    and isinstance(t.left.args[0], ast.Name) and t.left.args[0].id in parameters):
                raise Unsupported('Constructor branch is outside the scalar ndim profile')
            alias = t.left.func.value.id
            if alias in parameters or any(isinstance(n, ast.Name) and n.id == alias and isinstance(n.ctx, ast.Store)
                                          for n in ast.walk(constructor)):
                raise Unsupported('The NumPy name must not be shadowed in the constructor')
            if not any(isinstance(n, ast.Import) and any(a.name == 'numpy' and (a.asname or a.name) == alias
                       for a in n.names) for n in tree.body):
                raise Unsupported('Scalar ndim specialization requires the explicit NumPy import')
            assumptions.append('Constructor inputs are built-in floats; NumPy ndim reports zero for that scalar input. The array branch is outside this profile.')
            for statement in node.body:
                assignment(statement, initial, locals_, init_declarations)
        else:
            if isinstance(node, ast.Assign) and isinstance(node.value, ast.BinOp):
                raise Unsupported('Constructor arithmetic needs a separate numerical admission rule')
            assignment(node, initial, locals_, init_declarations)
    if not fields:
        raise Unsupported('Constructor initializes no scalar fields')
    returned = method.body[-1]
    if not (isinstance(returned, ast.Return) and isinstance(returned.value, ast.Tuple) and len(returned.value.elts) == 2
            and all(isinstance(n, ast.Attribute) and isinstance(n.value, ast.Name) and n.value.id == 'self'
                    and n.attr in fields for n in returned.value.elts)):
        raise Unsupported('Scalar API method must return two initialized state fields')
    states = [n.attr for n in returned.value.elts]
    method_args = [n.arg for n in method.args.args]
    if len(method_args) < 2 or method_args[0] != 'self':
        raise Unsupported('Scalar API update needs self and one measurement argument')
    optional = method_args[2:]
    fallback = {}
    for node in method.body:
        if isinstance(node, ast.If) and len(node.body) == 1 and isinstance(node.body[0], ast.Assign):
            a = node.body[0]
            if isinstance(a.value, ast.Attribute):
                fallback[a.targets[0].id] = a.value.attr
    if any(n not in fallback for n in optional):
        raise Unsupported('Every optional API argument needs a stored fallback')
    constants = {attribute: 1.0 for attribute in fallback.values()}
    written = set(states)
    for statement in method.body:
        for node in ast.walk(statement):
            if (isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name) and
                    node.value.id == 'self' and isinstance(node.ctx, ast.Load) and node.attr not in written):
                constants[node.attr] = 1.0
        written.update(node.attr for node in ast.walk(statement)
                       if isinstance(node, ast.Attribute) and isinstance(node.ctx, ast.Store))
    # Constants are placeholders only for validation of AST forms/defaults.
    # The generated API retains actual stored fields and explicit overrides.
    specialize(source, function, {'state': {n:'s'+str(i) for i,n in enumerate(states)},
        'constants': constants, 'sequence':['measurement']})
    values = {n:'s.'+n for n in fields}
    locals_ = {method_args[1]: method_args[1]}
    declarations = []
    for n in optional:
        locals_[n] = '('+n+'.getD s.'+fallback[n]+')'
    for node in method.body[:-1]:
        if docstring(node) or isinstance(node, ast.If):
            continue
        assignment(node, values, locals_, declarations)
    result = '('+', '.join(values[n] for n in states)+')'
    expanded = {}
    for name, value in declarations:
        expanded[name] = re.sub(r'\bf[0-9]+\b', lambda m: expanded[m[0]], value)
    conditions = [re.sub(r'\bf[0-9]+\b', lambda m: expanded[m[0]], d) for d in divisors]
    safe = ' ∧ '.join('('+d+'.isFinite = true ∧ ('+d+' == (0.0 : Float)) = false)' for d in conditions) or 'True'
    safe_names = {n: n if re.search(r'\b'+re.escape(n)+r'\b', safe) else '_'+n
                  for n in ['s', method_args[1], *optional]}
    def record(values):
        return '{ '+', '.join(n+' := '+values[n] for n in fields)+' }'
    lines = ['module', '', 'public import Workflow.Generated.Funs', '',
        '/-! Scalar constructor and full-state update lowered from the selected Python AST. -/',
        '', '@[expose] public section', '', 'namespace Workflow.SourceAPI', '', 'structure State where']
    lines += ['  '+n+' : Float' for n in fields]
    lines += ['', 'def constructor '+' '.join('('+n+' : Float)' for n in parameters)+' : State :=']
    lines += ['  let '+n+' := '+v for n,v in init_declarations]
    lines += ['  '+record(initial), '',
        'def update (s : State) ('+method_args[1]+' : Float) '+
        ' '.join('('+n+' : Option Float)' for n in optional)+' : (Float × Float) × State :=']
    lines += ['  let '+n+' := '+v for n,v in declarations]
    lines += ['  ('+result+', '+record(values)+')', '',
        'def encode (s : State) : '+rust_type+' :=',
        '  '+record({n:'s.'+n for n in fields}), '',
        'def Safe ('+safe_names['s']+' : State) ('+safe_names[method_args[1]]+' : Float) '+
        ' '.join('('+safe_names[n]+' : Option Float)' for n in optional)+' : Prop :=',
        '  '+safe, '', 'def Contract : Prop :=',
        '  (∀ '+' '.join(parameters)+',',
        '    '+rust_type+'.new '+' '.join(parameters)+' = .ok (encode (constructor '+' '.join(parameters)+')))',
        '  ∧ (∀ s '+method_args[1]+' '+' '.join(optional)+', Safe s '+method_args[1]+' '+' '.join(optional)+' →',
        '    '+rust_type+'.'+method_name+' (encode s) '+method_args[1]+' '+' '.join(optional),
        '      = .ok ((update s '+method_args[1]+' '+' '.join(optional)+').1,',
        '          encode (update s '+method_args[1]+' '+' '.join(optional)+').2))', '',
        'end Workflow.SourceAPI', '']
    return '\n'.join(lines), {'fields': fields, 'parameters': parameters, 'method': method_name,
        'state': states, 'options': fallback, 'assumptions': assumptions,
        'scope': 'Ordinary scalar instance fields and binary64 operation order. The Python execution domain requires built-in floats, the selected original bodies and a nonzero stored divisor; arrays, custom dispatch and module initialization are excluded.'}
