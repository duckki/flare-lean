"""Independent exact-reference expressions; parse syntax, never execute user code."""
import ast
import re
from fractions import Fraction


def rational_equivalence(program,specification):
    """Propose bounded total-field case analysis, including zero denominators.

    This is proof generation, not an algebraic oracle. Mathlib checks each branch
    and rejects false identities; no nonzero premise is added to the root.
    """
    if (not isinstance(specification,list) or program.math or program.arrays or program.scientific
            or len(program.nodes)>32):
        return None
    from .emit import expression
    values={f'a{i}':f'a{i}' for i in range(len(program.inputs))};denominators=[]
    for node in program.nodes:
        if sum(len(values[arg]) for arg in node.args)>32768:return None
        if node.op=='div':denominators.append(values[node.args[1]])
        values[node.name]=re.sub(r'\b[an]\d+\b',lambda m:'('+values[m[0]]+')',expression(node,ideal=True))
    for source in specification:
        for node in ast.walk(ast.parse(source,mode='eval')):
            if isinstance(node,ast.BinOp) and isinstance(node.op,ast.Div):
                denominators.append(lean_expression(ast.get_source_segment(source,node.right),program.inputs))
    denominators=list(dict.fromkeys(x for x in denominators if re.search(r'\ba\d+\b',x)))
    if not denominators or len(denominators)>4:return None
    cases=[f'by_cases denominator{i} : {value} = 0' for i,value in enumerate(denominators)]
    args=', '.join('denominator'+str(i) for i in range(len(cases)))
    return ['  all_goals ('+' <;> '.join(cases)+')',
            '  all_goals field_simp ['+args+']']


def lean_expression(source, inputs, bindings=None, allow_conditionals=False, allow_sqrt=False):
    names = bindings if bindings is not None else {name: f'a{i}' for i, name in enumerate(inputs)}

    def visit(node):
        if (allow_sqrt and isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == 'sqrt' and len(node.args) == 1 and not node.keywords):
            return '(Real.sqrt '+visit(node.args[0])+')'
        if allow_conditionals and isinstance(node, ast.IfExp):
            t = node.test
            if not (isinstance(t, ast.Compare) and len(t.ops) == 1 and type(t.ops[0]) in (ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
                raise ValueError('Exact conditional reference requires one ordered comparison')
            a, b = visit(t.left), visit(t.comparators[0])
            if isinstance(t.ops[0], (ast.Gt, ast.GtE)):
                a, b = b, a
            op = '<' if isinstance(t.ops[0], (ast.Lt, ast.Gt)) else '≤'
            return '(if '+a+' '+op+' '+b+' then '+visit(node.body)+' else '+visit(node.orelse)+')'
        if isinstance(node, ast.Name) and node.id in names:
            return names[node.id]
        if isinstance(node, ast.Constant) and type(node.value) in (int, float):
            value = Fraction(ast.get_source_segment(source, node))
            return f'({value.numerator} : ℝ)' if value.denominator == 1 else f'(({value.numerator} : ℝ) / {value.denominator})'
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return f'(-{visit(node.operand)})'
        if isinstance(node, ast.BinOp) and type(node.op) in (ast.Add, ast.Sub, ast.Mult, ast.Div):
            operator = {ast.Add: '+', ast.Sub: '-', ast.Mult: '*', ast.Div: '/'}[type(node.op)]
            return f'({visit(node.left)} {operator} {visit(node.right)})'
        raise ValueError('Exact reference supports original input names, rational constants, + - * / and selected mathematical primitives')

    return visit(ast.parse(source, mode='eval').body)


def validate(specification, program):
    if program.scientific:
        from .collection_spec import specification as collections
        collections(specification,program)
        return
    if program.counted:
        from .counted import specification as counted_specification
        counted_specification(specification,program)
        return
    if program.arrays:
        from .array_emit import matrix_specification
        matrix_specification(specification,program)
        return
    if isinstance(specification,list):
        if len(specification)!=len(program.outputs) or any(not isinstance(x,str) for x in specification):
            raise ValueError('Provide an independent exact expression string per output')
        for expression in specification: lean_expression(expression,program.inputs,allow_conditionals=bool(program.branches),allow_sqrt=bool(program.math and 'sqrt' in program.math['operations']))
        return
    fields={'kind','initial','sequence','state','element','step'}
    if not isinstance(specification,dict) or set(specification)!=fields or specification['kind']!='fold':
        raise ValueError('Exact specification must be an expression list or a two-state fold')
    if len(program.outputs)!=2:
        raise ValueError('Fold specifications require two state outputs')
    state=specification['state'];element=specification['element']
    if (not isinstance(state,list) or len(state)!=2 or any(not isinstance(x,str) or not x.isidentifier() for x in state)
            or not isinstance(element,str) or not element.isidentifier()
            or len(set([*state,element]))!=3 or set([*state,element])&set(program.inputs)):
        raise ValueError('Fold state and element names must be distinct identifiers, separate from original inputs')
    sequence=specification['sequence']
    if (not isinstance(sequence,list) or not 1<=len(sequence)<=128
            or any(not isinstance(x,str) or x not in program.inputs for x in sequence)):
        raise ValueError('Fold sequence must list 1 to 128 original input names in order')
    for field in ['initial','step']:
        expressions=specification[field]
        if not isinstance(expressions,list) or len(expressions)!=2 or any(not isinstance(x,str) for x in expressions):
            raise ValueError('Fold '+field+' must contain two exact expressions')
        names=program.inputs if field=='initial' else (*program.inputs,*state,element)
        for expression in expressions: lean_expression(expression,names)


def lean_specification(specification,program):
    if program.scientific:
        from .collection_spec import specification as collections
        return collections(specification,program)
    if program.arrays:
        from .array_emit import matrix_specification
        return [matrix_specification(specification,program)]
    if isinstance(specification,list):
        values=[lean_expression(x,program.inputs,allow_conditionals=bool(program.branches),allow_sqrt=bool(program.math and 'sqrt' in program.math['operations'])) for x in specification]
        return [values[0] if len(values)==1 else '('+', '.join(values)+')']
    names={name:f'a{i}' for i,name in enumerate(program.inputs)}
    initial='('+', '.join(lean_expression(x,program.inputs,allow_conditionals=bool(program.branches)) for x in specification['initial'])+')'
    bindings={**names,specification['state'][0]:'state.1',specification['state'][1]:'state.2',
              specification['element']:'observation'}
    step='('+', '.join(lean_expression(x,(),bindings) for x in specification['step'])+')'
    sequence='['+', '.join(names[x] for x in specification['sequence'])+']'
    return [sequence+'.foldl (fun (state : ℝ × ℝ) (observation : ℝ) =>',
            '  '+step+') '+initial]


def describe(specification):
    if isinstance(specification,list): return specification
    if specification.get('kind') == 'collections':
        return ['exact '+name+' = '+expression for name,expression in specification['bindings']]+['return '+expression for expression in specification['outputs']]
    if specification.get('kind') == 'matrix':
        return [specification['expression']+' (exact real matrix product)']
    if specification.get('kind') == 'iterate':
        return ['initial = '+', '.join(specification['initial']),
                'iterate at the selected original source count; state = '+', '.join(specification['state']),
                *specification['step']]
    return ['initial = '+', '.join(specification['initial']),
            'fold over '+', '.join(specification['sequence']),
            'state names = '+', '.join(specification['state'])+'; element = '+specification['element'],
            *specification['step']]


def sqrt_congruence(source):
    """Propose an equality proof for the reference's primitive structure.

    Arithmetic leaves use ring normalization. Congruence crosses sqrt calls;
    Lean still rejects a false argument equality or a different outer structure.
    """
    def contains(node):
        return any(isinstance(x,ast.Call) for x in ast.walk(node))
    def proof(node):
        if not contains(node):
            return '(by ring)'
        if isinstance(node,ast.Call):
            return '(congrArg Real.sqrt '+proof(node.args[0])+')'
        if isinstance(node,ast.UnaryOp):
            return '(congrArg (fun x : ℝ => -x) '+proof(node.operand)+')'
        if isinstance(node,ast.BinOp):
            op={ast.Add:'+',ast.Sub:'-',ast.Mult:'*',ast.Div:'/'}[type(node.op)]
            return '(congrArg₂ (fun x y : ℝ => x '+op+' y) '+proof(node.left)+' '+proof(node.right)+')'
        raise ValueError('Unsupported primitive reference proof structure')
    return proof(ast.parse(source,mode='eval').body)
