"""Independent exact-reference expressions; parse syntax, never execute user code."""
import ast
from fractions import Fraction


def lean_expression(source, inputs, bindings=None):
    names = bindings if bindings is not None else {name: f'a{i}' for i, name in enumerate(inputs)}

    def visit(node):
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
        raise ValueError('Exact reference supports only original input names, rational constants and + - * /')

    return visit(ast.parse(source, mode='eval').body)


def validate(specification, program):
    if program.arrays:
        from .array_emit import matrix_specification
        matrix_specification(specification,program)
        return
    if isinstance(specification,list):
        if len(specification)!=len(program.outputs) or any(not isinstance(x,str) for x in specification):
            raise ValueError('Provide an independent exact expression string per output')
        for expression in specification: lean_expression(expression,program.inputs)
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
    if program.arrays:
        from .array_emit import matrix_specification
        return [matrix_specification(specification,program)]
    if isinstance(specification,list):
        values=[lean_expression(x,program.inputs) for x in specification]
        return [values[0] if len(values)==1 else '('+', '.join(values)+')']
    names={name:f'a{i}' for i,name in enumerate(program.inputs)}
    initial='('+', '.join(lean_expression(x,program.inputs) for x in specification['initial'])+')'
    bindings={**names,specification['state'][0]:'state.1',specification['state'][1]:'state.2',
              specification['element']:'observation'}
    step='('+', '.join(lean_expression(x,(),bindings) for x in specification['step'])+')'
    sequence='['+', '.join(names[x] for x in specification['sequence'])+']'
    return [sequence+'.foldl (fun (state : ℝ × ℝ) (observation : ℝ) =>',
            '  '+step+') '+initial]


def describe(specification):
    if isinstance(specification,list): return specification
    if specification.get('kind') == 'matrix':
        return [specification['expression']+' (exact real matrix product)']
    return ['initial = '+', '.join(specification['initial']),
            'fold over '+', '.join(specification['sequence']),
            'state names = '+', '.join(specification['state'])+'; element = '+specification['element'],
            *specification['step']]
