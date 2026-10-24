"""C access/loop verification conditions and typed heap roots, proved in Lean."""
import re
from fractions import Fraction as Q

from numerics.emit.scalar import expression, projection, real


def buffers(program):
    return [p for p in program.c['api'] if p['kind']=='buffer']


def memory_profile(program):
    return program.c is not None and bool(buffers(program))


def parameters(program):
    result=['(heap : Flare.Binary64.Memory.Heap)']
    result += ['(p'+str(i)+' : Nat)' for i,_ in enumerate(buffers(program))]
    offset=0
    for p in program.c['api']:
        if p['kind']!='buffer':result += ['(a'+str(i)+' : Float)' for i in range(offset,offset+len(p['inputs']))]
        offset+=len(p['inputs'])
    return ' '.join(result)


def arguments(program):
    values=['heap',*['p'+str(i) for i,_ in enumerate(buffers(program))]]
    offset=0
    for p in program.c['api']:
        if p['kind']!='buffer':values += ['a'+str(i) for i in range(offset,offset+len(p['inputs']))]
        offset+=len(p['inputs'])
    return ' '.join(values)


def scalar_arguments(program):
    values=[];offset=0;pointer=0
    for p in program.c['api']:
        if p['kind']=='buffer':
            values += ['heap[p'+str(pointer)+' + '+str(i)+']!' for i in range(p['length'])];pointer+=1
        else:values += ['a'+str(i) for i in range(offset,offset+len(p['inputs']))]
        offset+=len(p['inputs'])
    return values


def memory_hypotheses(program):
    ps=buffers(program);result=[]
    for i,p in enumerate(ps):
        result.append('(valid'+str(i)+' : Flare.Binary64.Memory.valid heap p'+str(i)+' '+str(p['length'])+')')
    for i,p in enumerate(ps):
        for j,q in enumerate(ps[i+1:],i+1):
            if not p['readonly'] or not q['readonly']:
                result.append('(sep'+str(i)+'_'+str(j)+' : Flare.Binary64.Memory.separated p'+str(i)+' '+str(p['length'])+' p'+str(j)+' '+str(q['length'])+')')
    return result


def memory_facts(program):
    ps=buffers(program);lines=[];facts=[]
    for i,p in enumerate(ps):
        for k in range(p['length']):
            name='bound'+str(i)+'_'+str(k);facts.append(name)
            lines += ['  have '+name+' : p'+str(i)+' + '+str(k)+' < heap.size :=',
                      '    Flare.Binary64.Memory.region_index heap p'+str(i)+' '+str(p['length'])+' '+str(k)+' valid'+str(i)+' (by decide)']
    addresses=[(i,k) for i,p in enumerate(ps) for k in range(p['length'])]
    for n,(i,k) in enumerate(addresses):
        for j,l in addresses[n+1:]:
            if i!=j and ps[i]['readonly'] and ps[j]['readonly']:continue
            if i==j and k==l:continue
            name=f'ne{i}_{k}_{j}_{l}';facts.append(name)
            lines += [f'  have {name} : p{i}+{k} ≠ p{j}+{l} := by',
                      '    '+('omega' if i==j else f'exact Flare.Binary64.Memory.separated_indices p{i} {ps[i]["length"]} p{j} {ps[j]["length"]} {k} {l} sep{i}_{j} (by decide) (by decide)')]
    for i,p in enumerate(ps):
        for k in range(p['length']):
            lines += [f'  have rewrite_self{i}_{k} (mem : Flare.Binary64.Memory.Heap) (v : Float) (hi : p{i}+{k} < mem.size) :',
                      f'      (mem.set! (p{i}+{k}) v)[p{i}+{k}]! = v :=',
                      f'    Array.getElem!_set!_self mem (p{i}+{k}) v hi']
    for name in [n for n in facts if n.startswith('ne')]:
        i,k,j,l=map(int,re.findall(r'\d+',name))
        for reverse in [False,True]:
            left,right=(f'p{j}+{l}',f'p{i}+{k}') if reverse else (f'p{i}+{k}',f'p{j}+{l}')
            proof='(Ne.symm '+name+')' if reverse else name
            lines += ['  have rewrite_'+name+('_rev' if reverse else '')+' (mem : Flare.Binary64.Memory.Heap) (v : Float) :',
                      f'      (mem.set! ({left}) v)[{right}]! = mem[{right}]! :=',
                      '    Flare.Binary64.Memory.set_frame mem _ _ v '+proof]
    return lines,facts


def unused_lets(lines):
    text='\n'.join(lines)
    return [re.sub(r'^(\s*let )([A-Za-z][A-Za-z0-9_]*)(?=\s*(?::=|←))',
                   lambda m:m[1]+('_' if len(re.findall(r'\b'+m[2]+r'\b',text))==1 else '')+m[2],line) for line in lines]


def verification_conditions(program):
    return {'schema':'c-source-vcs-v1',
        'accesses':[{'line':step.get('line'),'buffer':step['buffer'],'index':step['index'],
                    'extent':next(p['length'] for p in buffers(program) if p['name']==step['buffer']),
                    'operation':step['kind']} for step in program.c['trace'] if step['kind'] in ('load','store')],
        'loops':program.c['loops'],
        'qualification':'Source-derived access and unsigned-counter conditions. Lean proves these and dynamic region/alias obligations; foreign solver verdicts do not discharge them.'}


def unused_parameters(source):
    lines=source.splitlines()
    for i,line in enumerate(lines):
        if not re.match(r'(?:noncomputable )?def ',line) or not line.endswith(':='):continue
        j=i+1
        while j<len(lines) and lines[j].startswith(' '):j+=1
        body='\n'.join(lines[i+1:j])
        lines[i]=re.sub(r'\(([A-Za-z_]\w*) :',lambda m:'('+('' if re.search(r'\b'+m[1]+r'\b',body) else '_')+m[1]+' :',line)
    return '\n'.join(lines)+'\n'


def model_source(program,request):
    from numerics.emit.scalar import kernel_source
    base=kernel_source(program,request['specification'])
    vcs=verification_conditions(program)
    checks=[f'decide (({a["index"]} : Nat) < {a["extent"]})' for a in vcs['accesses']]
    checks += [f'decide (({loop["iterations"]} : Nat) < 2^32)' for loop in vcs['loops']]
    lines=['','namespace Workflow','', 'def sourceConditions : Bool :=',
           '  '+(' && '.join('('+c+')' for c in checks) if checks else 'true'),'',
           'theorem sourceConditions_checked : sourceConditions = true := by decide +kernel','']
    if not memory_profile(program):
        return unused_parameters(base+'\n'.join([*lines,'end Workflow','']))
    ps=buffers(program);pmap={p['name']:'p'+str(i) for i,p in enumerate(ps)}
    args=arguments(program);scalars=scalar_arguments(program);nodes={n.name:n for n in program.nodes}
    void=program.c['return_type']=='void'
    typ='Flare.Binary64.Memory.Heap' if void else '(Flare.Binary64.Memory.Heap × Float)'
    lines += [f'def sourceExec {parameters(program)} : Option {typ} := do','  let mut mem := heap']
    mapping={}
    offset=0
    for p in program.c['api']:
        if p['kind']!='buffer':mapping.update({'a'+str(i):'a'+str(i) for i in range(offset,offset+len(p['inputs']))})
        offset+=len(p['inputs'])
    def subst(text):return re.sub(r'\b[an]\d+\b',lambda m:mapping[m[0]],text)
    for i,step in enumerate(program.c['trace']):
        if step['kind']=='node':
            n=nodes[step['node']];expr=subst(expression(n));mapping[n.name]=n.name
            lines.append('  let '+n.name+' := '+expr)
        elif step['kind']=='load':
            name='loaded'+str(i);mapping[step['ref']]=name
            lines.append('  let '+name+' ← Flare.Binary64.Memory.load mem ('+pmap[step['buffer']]+' + '+str(step['index'])+')')
        else:
            lines.append('  mem ← Flare.Binary64.Memory.store mem ('+pmap[step['buffer']]+' + '+str(step['index'])+') '+mapping[step['ref']])
    lines += ['  return '+('mem' if void else '(mem, '+mapping[program.outputs[0]]+')'),'']
    lines=unused_lets(lines)
    lines += [f'def postHeap {parameters(program)} : Flare.Binary64.Memory.Heap :=']
    for i,arg in enumerate(scalars):
        if arg!='a'+str(i):lines.append(f'  let a{i} := {arg}')
    lines += ['  let '+n.name+' := '+expression(n) for n in program.nodes]
    lines += ['  let mem := heap']
    for step in program.c['trace']:
        if step['kind']=='store':lines.append('  let mem := mem.set! ('+pmap[step['buffer']]+' + '+str(step['index'])+') '+step['ref'])
    lines += ['  mem','']
    # Renaming unused graph locals preserves evaluated source arithmetic without
    # suppressing Lean's unused-variable warnings.
    split=lines.index('def postHeap '+parameters(program)+' : Flare.Binary64.Memory.Heap :=')
    lines=lines[:split]+unused_lets(lines[split:])
    lines += [f'theorem source_equiv {parameters(program)}',*['    '+h for h in memory_hypotheses(program)],
              '    : sourceExec '+args+' = some '+('('+('postHeap '+args)+')' if void else '(heap, kernel '+' '.join('('+a+')' for a in scalars)+')')+' := by']
    proofs,facts=memory_facts(program);lines+=proofs
    lines += ['  simp only [sourceExec, '+('postHeap' if void else 'kernel')+']']
    rules=['Nat.add_zero','Flare.Binary64.Memory.load','ite_eq_left',
           'Option.bind_eq_bind','Option.bind_some','Option.pure_def']
    if any(s['kind']=='store' for s in program.c['trace']):
        rules += ['Flare.Binary64.Memory.store','Array.size_set!']
    lines += ['  simp_all only ['+', '.join(rules)+']']
    lines += ['', 'end Workflow','']
    return unused_parameters(base.replace('public import Flare.Binary64.Value','public import Flare.Binary64.Value\npublic import Flare.Binary64.Memory')+'\n'.join(lines))


def hypotheses(program,domain):
    values=memory_hypotheses(program)
    values += ['(h'+str(i)+' : ('+arg+').isFinite = true ∧ '+real(domain[name][0])+' ≤ value ('+arg+') ∧ value ('+arg+') ≤ '+real(domain[name][1])+')'
               for i,(name,arg) in enumerate(zip(program.inputs,scalar_arguments(program),strict=True))]
    return values


def conclusion(program,bounds,targets):
    ps=buffers(program);args=arguments(program);scalars=scalar_arguments(program)
    exact='specification '+' '.join('(value ('+v+'))' for v in scalars)
    clauses=['sourceConditions = true']
    void=program.c['return_type']=='void'
    if void:
        p=next(i for i,b in enumerate(ps) if b['name']==program.c['writable']);length=ps[p]['length']
        prefix='∃ final, sourceExec '+args+' = some final ∧ '
        clauses += ['final.size = heap.size',f'∀ index, index < heap.size → (index < p{p} ∨ p{p}+{length} ≤ index) → final[index]! = heap[index]!']
        actual=[f'final[p{p}+{i}]!' for i in range(length)]
    else:
        prefix='∃ output, sourceExec '+args+' = some (heap, output) ∧ '
        actual=['output']
    for i,(name,out) in enumerate(zip(program.outputs,actual,strict=True)):
        clauses += ['('+out+').isFinite = true', '|value ('+out+') - ('+exact+')'+projection(i,len(actual))+'| ≤ '+real(bounds[name].e)]
    if all(bounds[n].e<=Q(t['limit']) for n,t in zip(program.outputs,targets,strict=True)):
        clauses += [real(bounds[n].e)+' ≤ '+real(t['limit']) for n,t in zip(program.outputs,targets,strict=True)]
    return prefix+'\n      ∧ '.join('('+c+')' for c in clauses)


def scalar_conclusion(program,bounds,targets,with_rust=False):
    from numerics.emit.scalar import applied, proposition
    args=applied(program)
    clauses=proposition(program,bounds,output='output' if with_rust else 'kernel',exact='specification')
    if all(bounds[n].e<=Q(t['limit']) for n,t in zip(program.outputs,targets,strict=True)):
        clauses+=' ∧ ('+' ∧ '.join(real(bounds[n].e)+' ≤ '+real(t['limit']) for n,t in zip(program.outputs,targets,strict=True))+')'
    if with_rust:clauses='∃ output, Generated.kernel '+args+' = .ok output ∧ '+clauses
    return 'sourceConditions = true ∧ ('+clauses+')'


def proof_source(program,domain,bounds,targets,with_rust=False):
    if not memory_profile(program):
        from numerics.emit.scalar import applied, hypotheses as scalar_hypotheses, params
        args=applied(program)
        return '\n'.join(['','namespace Workflow.Certificate','open Flare.Binary64.Value','',
            'theorem certificate '+params(program),*['    '+h for h in scalar_hypotheses(program,domain)],
            '    : '+scalar_conclusion(program,bounds,targets,with_rust)+' := by',
            '  exact ⟨sourceConditions_checked, scalar_certificate '+args+' '+
            ' '.join('h'+str(i) for i in range(len(program.inputs)))+'⟩','', 'end Workflow.Certificate',''])
    args=arguments(program);scalars=scalar_arguments(program);ps=buffers(program)
    call='scalar_certificate '+' '.join('('+v+')' for v in scalars)+' '+' '.join('h'+str(i) for i in range(len(scalars)))
    memargs=' '.join(re.findall(r'\(([A-Za-z_]\w*) :', ' '.join(memory_hypotheses(program))))
    lines=['','namespace Workflow.Certificate','open Flare.Binary64.Value','',
           'theorem certificate '+parameters(program),*['    '+h for h in hypotheses(program,domain)],
           '    : '+conclusion(program,bounds,targets)+' := by',
           '  have numerical := '+call]
    if program.c['return_type']=='void':
        lines += ['  refine ⟨postHeap '+args+', source_equiv '+args+' '+memargs+', sourceConditions_checked, ?_⟩',
                  '  constructor','  · simp only [postHeap, Array.size_set!]' ,'  constructor',
                  '  · intro index _ outside']
        p=next(i for i,b in enumerate(ps) if b['name']==program.c['writable'])
        frame=[]
        for k in range(ps[p]['length']):
            name='frame'+str(k);frame.append(name)
            lines += [f'    have {name} : p{p}+{k} ≠ index := by omega']
        for k,name in enumerate(frame):
            lines += [f'    have rewrite_frame{k} (mem : Flare.Binary64.Memory.Heap) (v : Float) :',
                      f'        (mem.set! (p{p}+{k}) v)[index]! = mem[index]! :=',
                      '      Flare.Binary64.Memory.set_frame mem _ _ v '+name]
        lines += ['    simp only [postHeap]', '    simp_all only [Nat.add_zero]']
        proofs,facts=memory_facts(program);lines+=proofs
        lines += ['  simp only [postHeap]', '  simp_all only [kernel, Nat.add_zero, Array.size_set!, and_self]']
    else:
        lines += ['  exact ⟨kernel '+' '.join('('+v+')' for v in scalars)+', source_equiv '+args+' '+memargs+', sourceConditions_checked, numerical⟩']
    lines += ['','end Workflow.Certificate','']
    return '\n'.join(lines)


def check_source(program,domain,bounds,targets,with_rust=False):
    if not memory_profile(program):
        from numerics.emit.scalar import applied, params, hypotheses as scalar_hypotheses
        declaration=params(program);hyps=scalar_hypotheses(program,domain)
        args=applied(program)+' '+' '.join('h'+str(i) for i in range(len(program.inputs)))
        expected=scalar_conclusion(program,bounds,targets,with_rust)
    else:
        declaration=parameters(program);hyps=hypotheses(program,domain)
        args=arguments(program)+' '+' '.join(re.findall(r'\(([A-Za-z_]\w*) :',' '.join(hyps)))
        expected=conclusion(program,bounds,targets)
    return '\n'.join(['module','','import all Workflow.Proof','meta import Lean.Util.CollectAxioms','',
        'open Workflow Flare.Binary64.Value','', 'example '+declaration,
        *['    '+h for h in hyps],'    : '+expected+' :=',
        '  Workflow.Certificate.certificate '+args,'',
        'open Lean in','run_cmd do','  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]',
        '  for axiomName in ← Lean.collectAxioms ``Workflow.Certificate.certificate do',
        '    unless allowed.contains axiomName do',
        '      throwError "Unexpected axiom {axiomName} in root certificate"',
        '  logInfo "C root type and transitive axioms checked independently."',''])

