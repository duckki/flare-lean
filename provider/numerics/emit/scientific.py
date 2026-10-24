"""Typed collection execution, shape/access roots and optional actual Rust return."""
from fractions import Fraction as Q
from numerics.frontends.scientific import admit, count


def parameters(program):
    return ' '.join(f'(p{i} : '+('Flare.Binary64.Collection.Tensor' if field['shape'] else 'Float')+')' for i,field in enumerate(program.scientific['inputs']))


def arguments(program):return ' '.join('p'+str(i) for i in range(len(program.scientific['inputs'])))


def cells(program):
    return [f'(p{i}.data.getD {j} 0.0)' if field['shape'] else f'p{i}' for i,field in enumerate(program.scientific['inputs']) for j in range(count(field['shape']))]


def guards(program):return [f'(p{i}.shape = {field["shape"]} ∧ p{i}.data.size = {count(field["shape"])})' for i,field in enumerate(program.scientific['inputs']) if field['shape']]


def hypotheses(program,domain):
    from numerics.emit.scalar import real
    result=[f'(shape{i} : p{i}.shape = {field["shape"]} ∧ p{i}.data.size = {count(field["shape"])})' for i,field in enumerate(program.scientific['inputs']) if field['shape']]
    return result+[f'(h{i} : {cell}.isFinite = true ∧ {real(domain[name][0])} ≤ value {cell} ∧ value {cell} ≤ {real(domain[name][1])})' for i,(name,cell) in enumerate(zip(program.inputs,cells(program),strict=True))]


def model_source(program,request,source):
    from numerics.emit.scalar import kernel_source, projection
    lines=[]
    from numerics.frontends.module_selection import selected_source
    from dataclasses import replace
    modeled=admit(selected_source(program,source),program.function,request['scientific_arrays'],program.language,lines)
    if replace(modeled,selection=program.selection)!=program:raise ValueError('Scientific source model changed')
    base=kernel_source(program,request['specification']).replace('public import Flare.Binary64.Value','public import Flare.Binary64.Value\npublic import Flare.Binary64.Collection\npublic import Mathlib.LinearAlgebra.Matrix.Notation')
    args=arguments(program);scalars=cells(program);call='kernel '+' '.join(scalars)
    conditions=[f'decide (({a["index"]} : Nat) < {a["extent"]})' for a in program.scientific['accesses']]
    conditions += [f'decide (({a["stop"]} : Nat) ≤ 32)' for a in program.scientific['loops']]
    extra=['','namespace Workflow','',f'def inputShapes {parameters(program)} : Bool :=',
           '  '+(' && '.join('('+g.replace(' = ',' == ').replace(' ∧ ',' && ')+')' for g in guards(program)) or 'true'),
           '','def sourceConditions : Bool :=','  '+(' && '.join(conditions) if conditions else 'true'),
           '','theorem sourceConditions_checked : sourceConditions = true := by decide +kernel','',
           f'def collectionOutputs {parameters(program)} : Array Flare.Binary64.Collection.Tensor :=',*lines,'',
           f'def collectionKernel {parameters(program)} : Array Float :=',
           f'  (collectionOutputs {args}).foldl (fun acc tensor => acc ++ tensor.data) #[]','',
           f'def sourceExec {parameters(program)} : Option (Array Flare.Binary64.Collection.Tensor) :=',f'  if inputShapes {args} then some (collectionOutputs {args}) else none','',
           f'theorem collection_equiv {parameters(program)} : collectionKernel {args} =',
           '    #['+', '.join(f'({call})'+projection(i,len(program.outputs)) for i in range(len(program.outputs)))+'] := by',
           *(['  have empty : Array.range 0 = #[] := Array.range_eq_empty_iff.mpr rfl'] if 'Flare.Binary64.Collection.' in '\n'.join(lines) else []),
           '  simp [collectionKernel, collectionOutputs, kernel'+''.join(', '+name for name in ['Flare.Binary64.Collection.binary','Flare.Binary64.Collection.outer','Flare.Binary64.Collection.transpose'] if name in '\n'.join(lines))+
           (', Array.range_succ, empty' if 'Flare.Binary64.Collection.' in '\n'.join(lines) else '')+
           (', Array.set!_eq_setIfInBounds' if '.set!' in '\n'.join(lines) else '')+']','','end Workflow','']
    # Unused scalar parameters/locals keep their operation but do not suppress warnings.
    from numerics.emit.c import unused_parameters
    return unused_parameters(base+'\n'.join(extra))


def conclusion(program,bounds,targets,with_rust=False):
    from numerics.emit.scalar import real, projection
    args=arguments(program);scalars=cells(program);n=len(program.outputs)
    clauses=[f'inputShapes {args} = true','sourceConditions = true',f'sourceExec {args} = some (collectionOutputs {args})',
             f'(collectionKernel {args}).size = {n}',f'(collectionOutputs {args}).size = {len(program.scientific["outputs"])}']
    for i,dims in enumerate(program.scientific['outputs']):
        tensor=f'((collectionOutputs {args}).getD {i} default)'
        clauses += [tensor+'.shape = '+str(dims),tensor+'.data.size = '+str(count(dims))]
    if with_rust:clauses.append('output = kernel '+' '.join(scalars))
    for i,name in enumerate(program.outputs):
        result=f'(collectionKernel {args}).getD {i} 0.0'
        exact='(specification '+' '.join('(value '+c+')' for c in scalars)+')'+projection(i,n)
        clauses += ['('+result+').isFinite = true',f'|value ({result}) - {exact}| ≤ {real(bounds[name].e)}']
    if all(bounds[n].e<=Q(t['limit']) for n,t in zip(program.outputs,targets,strict=True)):
        clauses += [real(bounds[n].e)+' ≤ '+real(t['limit']) for n,t in zip(program.outputs,targets,strict=True)]
    expression='\n      ∧ '.join('('+c+')' for c in clauses)
    return ('∃ output, Generated.kernel '+' '.join(scalars)+' = .ok output ∧ '+expression) if with_rust else expression


def proof_source(program,domain,bounds,targets,with_rust=False):
    args=arguments(program);scalars=cells(program)
    call='scalar_certificate '+' '.join(scalars)+' '+' '.join('h'+str(i) for i in range(len(scalars)))
    lines=['','namespace Workflow.Certificate','open Flare.Binary64.Value','',f'theorem certificate {parameters(program)}',
        *['    '+h for h in hypotheses(program,domain)],'    : '+conclusion(program,bounds,targets,with_rust)+' := by',
        '  have numerical := '+call]
    if with_rust:
        lines += ['  rcases numerical with ⟨output, extracted, accuracy⟩',
                  '  have extracted_eq := source_equiv '+' '.join(scalars),
                  '  rw [extracted] at extracted_eq','  have same : output = kernel '+' '.join(scalars)+' := by simpa using extracted_eq',
                  '  refine ⟨output, extracted, ?_⟩', '  rw [same] at accuracy ⊢']
        numerical='accuracy'
    else:numerical='numerical'
    shape_names=['shape'+str(i) for i,f in enumerate(program.scientific['inputs']) if f['shape']]
    shape_proof=shape_names[0] if shape_names else 'rfl'
    for name in shape_names[1:]:shape_proof='⟨'+shape_proof+', '+name+'⟩'
    lines += ['  have shaped : inputShapes '+args+' = true := by',
              '    simp only [inputShapes, Bool.and_eq_true, beq_iff_eq]',
              '    exact '+shape_proof,
              '  refine ⟨shaped, sourceConditions_checked, ?_, ?_, '+', '.join(['?_']*(1+2*len(program.scientific['outputs'])))+', '+('rfl, ' if with_rust else '')+'?_⟩',
              '  · simp only [sourceExec, shaped, ite_true]',
              '  · rw [collection_equiv]; rfl',
              '  · simp [collectionOutputs]',
              *sum((['  · simp [collectionOutputs]', '  · simp [collectionOutputs]'] for _ in program.scientific['outputs']),[]),
              '  · simpa [collection_equiv] using '+numerical,
              '','end Workflow.Certificate','']
    return '\n'.join(lines)


def check_source(program,domain,bounds,targets,with_rust=False):
    import re
    hyps=hypotheses(program,domain)
    text='\n'.join(['module','','import all Workflow.Proof','meta import Lean.Util.CollectAxioms','',
        'open Workflow Flare.Binary64.Value','',f'example {parameters(program)}',*['    '+h for h in hyps],
        '    : '+conclusion(program,bounds,targets,with_rust)+' :=',
        '  Workflow.Certificate.certificate '+arguments(program)+' '+' '.join(re.findall(r'\(([A-Za-z_]\w*) :',' '.join(hyps))),'',
        'open Lean in','run_cmd do','  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]',
        '  for axiomName in ← Lean.collectAxioms ``Workflow.Certificate.certificate do',
        '    unless allowed.contains axiomName do','      throwError "Unexpected axiom {axiomName} in root certificate"',
        '  logInfo "Scientific collection root and transitive axioms checked independently."',''])
    return text
