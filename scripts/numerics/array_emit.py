"""Typed array roots and independent real matrix specifications for fixed products."""
import ast
from fractions import Fraction as Q

from .python_arrays import access, input_names, parse_arrays, paths


def matrix_specification(specification, program):
    from .emit import returned
    if (not isinstance(specification,dict) or set(specification)!={'kind','expression'} or
            specification['kind']!='matrix' or not isinstance(specification['expression'],str)):
        raise ValueError('Array requests require an independent matrix specification: kind and expression')
    inputs={};offset=0
    for field in program.arrays['inputs']:
        dims=field['shape'];r=dims[0];c=dims[1] if len(dims)==2 else 1
        literal='!!['+'; '.join(', '.join('a'+str(offset+i*c+j) for j in range(c)) for i in range(r))+']'
        inputs[field['name']]=(literal,(r,c));offset+=r*c
    def visit(node):
        if isinstance(node,ast.Name) and node.id in inputs: return inputs[node.id]
        if isinstance(node,ast.BinOp) and isinstance(node.op,(ast.MatMult,ast.Add,ast.Sub)):
            left,ls=visit(node.left);right,rs=visit(node.right)
            if isinstance(node.op,ast.MatMult):
                if ls[1]!=rs[0]: raise ValueError('Exact matrix product has incompatible shapes')
                dims=(ls[0],rs[1]);op='*'
            else:
                if ls!=rs: raise ValueError('Exact matrix addition has incompatible shapes')
                dims=ls;op='+' if isinstance(node.op,ast.Add) else '-'
            return '('+left+' '+op+' '+right+')',dims
        raise ValueError('Exact matrix expressions support original arrays, @, + and - only')
    expression,dims=visit(ast.parse(specification['expression'],mode='eval').body)
    rows,_,columns=program.arrays['product']
    if dims!=(rows,columns): raise ValueError('Exact specification output shape disagrees with the source')
    return returned([f'({expression}) ⟨{i}, by decide⟩ ⟨{j}, by decide⟩'
                     for i in range(rows) for j in range(columns)])


def parameters(program,used=None):
    return ' '.join('('+('_' if used is not None and i!=used else '')+'p'+str(i)+' : '+('Array Float' if len(field['shape'])==1 else 'Array (Array Float)')+')'
                    for i,field in enumerate(program.arrays['inputs']))


def arguments(program):
    return ' '.join('p'+str(i) for i in range(len(program.arrays['inputs'])))


def scalar_arguments(program):
    return [access('p'+str(i),index) for i,field in enumerate(program.arrays['inputs'])
            for index in paths(field['shape'])]


def shaped_arguments(program, domain):
    from .emit import real
    result=[]
    for i,field in enumerate(program.arrays['inputs']):
        dims=field['shape'];clause=f'p{i}.size = {dims[0]}'
        if len(dims)==2: clause+=f' ∧ ∀ row ∈ p{i}.toList, row.size = {dims[1]}'
        result.append(f'(shape{i} : {clause})')
    for i,(name,arg) in enumerate(zip(program.inputs,scalar_arguments(program),strict=True)):
        result.append(f'(h{i} : {arg}.isFinite = true ∧ {real(domain[name][0])} ≤ value {arg} ∧ value {arg} ≤ {real(domain[name][1])})')
    return result


def kernel_source(program,request,source):
    from .emit import kernel_source as scalar_kernel, projection
    body=[]
    if parse_arrays(source,program.function,request['python_arrays'],body)!=program:
        raise ValueError('Array model does not match admitted source')
    result=scalar_kernel(program,request['specification'])
    args=arguments(program);scalars=scalar_arguments(program);call='kernel '+' '.join(scalars)
    dims=program.arrays['output_shape'];count=len(program.outputs)
    native=[f'({call})'+projection(i,count) for i in range(count)]
    value='#['+', '.join(native)+']' if len(dims)==1 else '#['+', '.join(
        '#['+', '.join(native[i*dims[1]:(i+1)*dims[1]])+']' for i in range(dims[0]))+']'
    guards=[]
    for p,field in enumerate(program.arrays['inputs']):
        ds=field['shape'];guard=f'p{p}.size == {ds[0]}'
        if len(ds)==2: guard+=f' && p{p}.all (fun row => row.size == {ds[1]})'
        guards.append('('+guard+')')
    lines=['','namespace Workflow','',f'def inputShapes {parameters(program)} : Bool :=',
           '  '+' && '.join(guards),'',f'def arrayKernel {parameters(program)} :=',*body,'']
    offset=0
    for p,field in enumerate(program.arrays['inputs']):
        count_inputs=len(input_names(field['name'],field['shape']))
        lines += [f'def storage{p} {parameters(program,used=p)} : Array Float :=',
                  '  #['+', '.join(scalars[offset:offset+count_inputs])+']','']
        offset+=count_inputs
    lines += [f'theorem array_equiv {parameters(program)} : arrayKernel {args} = {value} := by',
              '  simp [arrayKernel, kernel, Array.set!_eq_setIfInBounds]','']
    rows,inner,columns=program.arrays['product']
    lines += [f'theorem ordered_equiv {parameters(program)} :',
        f'    Flare.Matrix.OrderedProduct.product {rows} {inner} {columns} (storage0 {args}) (storage1 {args}) =',
        '      #['+', '.join(native)+'] := by',
        '  have empty : Array.range 0 = #[] := Array.range_eq_empty_iff.mpr rfl',
        '  have zero : Float.ofBits 0 = (0.0 : Float) := by rfl',
        '  simp [Flare.Matrix.OrderedProduct.product, Flare.Matrix.OrderedProduct.dot,',
        '    storage0, storage1, kernel, Array.range_succ, empty, zero,',
        '    List.range_succ, Flare.Matrix.Dense.entry]','','end Workflow','']
    return result+'\n'.join(lines)


def conclusion(program,bounds,targets):
    from .emit import real,projection
    args=arguments(program);scalars=scalar_arguments(program)
    native=f'(arrayKernel {args})';dims=program.arrays['output_shape'];count=len(program.outputs)
    # The return storage is always fresh and rectangular, with no default reads
    # reachable under these explicit shape/index facts.
    clauses=[f'{native}.size = {dims[0]}']
    if len(dims)==2: clauses.append(f'∀ row ∈ {native}.toList, row.size = {dims[1]}')
    outputs=[access(native,index) for index in paths(dims)]
    flattened='#['+', '.join(outputs)+']'
    rows,inner,columns=program.arrays['product']
    clauses.insert(0,f'Flare.Matrix.Operations.multiply {rows} {inner} {columns} (storage0 {args}) (storage1 {args}) = .ok {flattened}')
    clauses.insert(0,f'inputShapes {args} = true')
    for i,(name,out) in enumerate(zip(program.outputs,outputs,strict=True)):
        exact='(specification '+' '.join('(value '+a+')' for a in scalars)+')'+projection(i,count)
        clauses += [f'{out}.isFinite = true',f'|value {out} - {exact}| ≤ {real(bounds[name].e)}']
    if all(bounds[name].e<=Q(target['limit']) for name,target in zip(program.outputs,targets,strict=True)):
        clauses += [real(bounds[name].e)+' ≤ '+real(target['limit']) for name,target in zip(program.outputs,targets,strict=True)]
    return '\n      ∧ '.join('('+clause+')' for clause in clauses)


def proof_source(program,domain,bounds,targets):
    from .emit import real
    args=arguments(program);scalars=scalar_arguments(program)
    rows,inner,columns=program.arrays['product'];left_count=rows*inner
    magnitudes=[max(abs(Q(domain[name][0])),abs(Q(domain[name][1]))) for name in program.inputs]
    maximum=max(magnitudes[:left_count])*max(magnitudes[left_count:]);exponent=0
    while Q(2)**exponent<maximum: exponent+=1
    lines=['','namespace Workflow.Certificate','',
           'open Flare.Binary64.Value Flare.Binary64.Pipeline','',
           f'theorem certificate {parameters(program)}',
           *['    '+h for h in shaped_arguments(program,domain)],
           '    : '+conclusion(program,bounds,targets)+' := by',
           '  have numerical := scalar_certificate '+' '.join(scalars)+' '+
               ' '.join('h'+str(i) for i in range(len(scalars)))]
    for i,arg in enumerate(scalars):
        lines += [f'  have bound{i} : |value {arg}| ≤ {real(magnitudes[i])} := by',
                  f'    rw [abs_le]; constructor <;> linarith only [h{i}.2.1, h{i}.2.2]']
    for p,(start,stop) in enumerate([(0,left_count),(left_count,len(scalars))]):
        lines += [f'  have finite{p} : (storage{p} {args}).all Float.isFinite = true := by',
                  f'    simpa [storage{p}] using (show '+
                  ' ∧ '.join(scalars[i]+'.isFinite = true' for i in range(start,stop))+
                  ' from '+('⟨'+', '.join(f'h{i}.1' for i in range(start,stop))+'⟩' if stop-start>1 else f'h{start}.1')+')']
    lines += [f'  obtain ⟨result, success, _, _, _⟩ := Flare.Matrix.Multiplication.multiply_accuracy {rows} {inner} {columns}',
              f'    (storage0 {args}) (storage1 {args}) {exponent} (by norm_num) (by norm_num) (by norm_num)',
              '    finite0 finite1 (by','      intro i j k hi hj hk',
              '      interval_cases i'+(' <;> ' if rows>1 else '; ')+'interval_cases j'+
                  (' <;> ' if rows*columns>1 else '; ')+'interval_cases k']
    for i in range(rows):
        for j in range(columns):
            for k in range(inner):
                l=i*inner+k;r=left_count+k*columns+j
                lines += [f'      · simpa [Flare.Matrix.Dense.entry, storage0, storage1] using',
                          f'          (abs_product bound{l} bound{r}).trans (by norm_num :',
                          f'            {real(magnitudes[l])} * {real(magnitudes[r])} ≤ (2 : ℝ) ^ ({exponent} : Int))']
    lines[-1]+=')'
    meets=all(bounds[name].e<=Q(target['limit']) for name,target in zip(program.outputs,targets,strict=True))
    names=sum(([f'f{i}',f'e{i}'] for i in range(len(program.outputs))),[])
    lines += ['  rcases numerical with ⟨'+', '.join(names+(['_'] if meets else []))+'⟩',
              f'  have dense : Flare.Matrix.Dense.multiply {rows} {inner} {columns} (storage0 {args}) (storage1 {args}) = .ok result := by',
              f'    cases h : Flare.Matrix.Dense.multiply {rows} {inner} {columns} (storage0 {args}) (storage1 {args}) with',
              '    | error e => cases e <;> simp [Flare.Matrix.Operations.multiply, Flare.Matrix.Operations.adapt, h] at success',
              '    | ok value => simpa [Flare.Matrix.Operations.multiply, Flare.Matrix.Operations.adapt, h] using success',
              f'  have ordered := Flare.Matrix.OrderedProduct.multiply_eq {rows} {inner} {columns} _ _ _ dense',
              f'  rw [ordered, ordered_equiv] at success',
              '  refine ⟨'+', '.join(['?_']*(3+(len(program.arrays['output_shape'])==2)+len(names)+(len(targets) if meets else 0)))+'⟩',
              '  · simp only [inputShapes, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]',
              ('    refine ⟨⟨shape0.1, ?_⟩, ⟨shape1.1, ?_⟩⟩' if len(program.arrays['inputs'][1]['shape'])==2 else
               '    refine ⟨⟨shape0.1, ?_⟩, shape1⟩'),
              '    · intro i hi; exact shape0.2 _ (Array.getElem_mem_toList hi)',
              *(['    · intro i hi; exact shape1.2 _ (Array.getElem_mem_toList hi)']
                if len(program.arrays['inputs'][1]['shape'])==2 else []),
              '  · simpa [array_equiv] using success',
              '  · rw [array_equiv]; rfl']
    if len(program.arrays['output_shape'])==2:
        lines += ['  · rw [array_equiv]; simp']
    for name in names:
        lines += ['  · simpa [array_equiv] using '+name]
    if meets:
        lines += ['  · norm_num']*len(targets)
    lines += ['','end Workflow.Certificate','']
    return '\n'.join(lines)


def check_source(program,domain,bounds,targets):
    return '\n'.join(['module','','import all Workflow.Proof','meta import Lean.Util.CollectAxioms','',
        'open Workflow Flare.Binary64.Value','',f'example {parameters(program)}',
        *['    '+h for h in shaped_arguments(program,domain)],'    : '+conclusion(program,bounds,targets)+' :=',
        '  Workflow.Certificate.certificate '+arguments(program)+' '+
        ' '.join('shape'+str(i) for i in range(2))+' '+
        ' '.join('h'+str(i) for i in range(len(program.inputs))),'',
        'open Lean in','run_cmd do','  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]',
        '  for axiomName in ← Lean.collectAxioms ``Workflow.Certificate.certificate do',
        '    unless allowed.contains axiomName do',
        '      throwError "Unexpected axiom {axiomName} in root certificate"',
        '  logInfo "Array root type and transitive axioms checked independently."',''])
