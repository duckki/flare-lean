"""CBMC proposes scalar positivity witnesses; the ordinary Lean route checks them.

The C harness is search assistance, not a proved source translation. No witness,
timeout, unsupported model or rejected Lean root ever becomes a positive proof.
"""
from fractions import Fraction as Q
import json
import math
from pathlib import Path
import re
import time

from numerics.frontends.scalar import Unsupported, number
from numerics.workflow.certification import Runner, prepare, save, seal, sha


VERSION='6.11.0'


class SearchUnresolved(ValueError):
    def __init__(self,kind,message):
        super().__init__(message);self.kind=kind


def validate(request,program):
    selection=request['counterexample_search']
    if (not isinstance(selection,dict) or set(selection)!={'tool','output'} or selection['tool']!='cbmc'
            or type(selection['output']) is not int or not 0<=selection['output']<len(program.outputs)):
        raise Unsupported('counterexample_search needs tool cbmc and a zero-based output index')
    if 'counterexample' in request:raise ValueError('Choose supplied witnesses or search, not both')
    from numerics.workflow.counterexample import validate_request
    validate_request({**request,'counterexample':{'inputs':{n:'0x0000000000000000' for n in program.inputs},
                                                'output':selection['output']}},program)
    outputs=request.get('outputs',[])
    if len(outputs)==len(program.outputs) and outputs[selection['output']].get('property')!='strict_positive':
        raise Unsupported('CBMC search currently proposes strict-positivity failures only')
    if len(program.inputs)>8:raise Unsupported('CBMC search admits at most eight original scalar inputs')
    tools=request.get('search_tools',{})
    if not isinstance(tools,dict) or set(tools)!={'cbmc'} or not isinstance(tools['cbmc'],dict) or set(tools['cbmc'])!={'path'} or not isinstance(tools['cbmc']['path'],str):
        raise ValueError('Select the CBMC executable explicitly in search_tools.cbmc.path')


def endpoint(value,lower):
    exact=Q(value)
    try:rounded=float(exact)
    except OverflowError:rounded=-math.inf if exact<0 else math.inf
    if math.isfinite(rounded):
        if (lower and Q.from_float(rounded)<exact) or (not lower and Q.from_float(rounded)>exact):
            rounded=math.nextafter(rounded,math.inf if lower else -math.inf)
    return rounded.hex() if math.isfinite(rounded) else ('-__builtin_inf()' if rounded<0 else '__builtin_inf()')


def harness(program,request):
    lines=['#include <stdint.h>','#include <assert.h>','uint64_t nondet_u64(void);',
           'int main(void) {']
    for i,name in enumerate(program.inputs):
        lo,hi=request['domain'][name]
        lines += [f'  uint64_t flare_input_bits{i}=nondet_u64();',
            f'  union {{uint64_t bits; double value;}} input{i}={{.bits=flare_input_bits{i}}};',
            f'  __CPROVER_assume((flare_input_bits{i}&0x7ff0000000000000ULL)!=0x7ff0000000000000ULL);',
            f'  double a{i}=input{i}.value;',f'  __CPROVER_assume(a{i}>={endpoint(lo,True)} && a{i}<={endpoint(hi,False)});']
    for node in program.nodes:
        if node.op=='constant':value=number(node.bits).hex()
        elif node.op=='neg':value='-'+node.args[0]
        else:value=(' '+{'add':'+','sub':'-','mul':'*','div':'/'}[node.op]+' ').join(node.args)
        lines += [f'  double {node.name}={value};']
    lines += ['  assert('+program.outputs[request['counterexample_search']['output']]+' > 0.0);','}']
    return '\n'.join(lines)+'\n'


def witness(text,inputs):
    if len(text)>64_000_000:raise ValueError('CBMC JSON trace exceeds the admitted resource limit')
    records=json.loads(text)
    if not isinstance(records,list):raise ValueError('CBMC JSON UI must return a list')
    if any(not isinstance(item,dict) or not isinstance(item.get('result',[]),list) for item in records):
        raise ValueError('Malformed CBMC result records')
    results=[r for item in records for r in item.get('result',[])]
    if any(not isinstance(r,dict) for r in results):raise ValueError('Malformed CBMC property record')
    failures=[r for r in results if r.get('status')=='FAILURE' and r.get('property')=='main.assertion.1']
    if len(failures)!=1:raise SearchUnresolved('no_witness','No unique positivity failure trace; no certificate was produced')
    values={}
    trace=failures[0].get('trace',[])
    if not isinstance(trace,list) or any(not isinstance(s,dict) for s in trace):raise ValueError('Malformed CBMC trace')
    for step in trace:
        if step.get('stepType')!='assignment' or step.get('hidden',False) or step.get('internal',False):continue
        lhs=step.get('lhs','')
        if not isinstance(lhs,str):raise ValueError('Malformed CBMC assignment')
        match=re.fullmatch('flare_input_bits([0-9]+)',lhs)
        if not match:continue
        index=int(match[1]);value=step.get('value',{})
        if (not isinstance(value,dict) or index>=len(inputs) or index in values or value.get('width')!=64
                or not isinstance(value.get('binary'),str) or not re.fullmatch('[01]{64}',value['binary'])):
            raise ValueError('Malformed or ambiguous CBMC input assignment')
        values[index]='0x'+format(int(value['binary'],2),'016x')
    if set(values)!=set(range(len(inputs))):raise ValueError('CBMC trace omits original input words')
    return {name:values[i] for i,name in enumerate(inputs)}


def produce(session):
    program,request,output,runner=session.program,session.request,session.output,session.runner
    configured=str(Path(request['search_tools']['cbmc']['path']).expanduser().resolve())
    tool,_=session.tool('cbmc',['--version'],
        r'\A(\d+\.\d+\.\d+)(?: \(cbmc-\1\))?\s*\Z',[VERSION],
        selection={'executable':configured})
    save(output/'search-tool.json',session.evidence['tools'][-1])
    (output/'search.c').write_text(harness(program,request))
    try:
        text=runner.run('cbmc-search',[tool,output/'search.c','--json-ui','--trace','--floatbv',
            '--round-to-nearest','--no-standard-checks'],phase='analysis')
    except RuntimeError:
        run=json.loads((output/'runs/cbmc-search/run.json').read_text())
        if run.get('status')!='completed' or run.get('returncode')!=10:raise
        text=(output/'runs/cbmc-search/stdout.txt').read_text()
    words=witness(text,program.inputs);save(output/'proposed-inputs.json',words)
    return words,{'trace':'runs/cbmc-search/stdout.txt','inputs':'proposed-inputs.json',
        'qualification':'Untrusted witness words; ordinary source admission and Lean checking establish any violation.'}


def certify(request_path,output):
    request,source,program,questions=prepare(request_path)
    if questions:return {'status':'needs_input','questions':questions}
    original=source.read_bytes()
    from numerics.frontends.scalar import parse
    if parse(program.language,original.decode(),program.function,python_module=request.get('python_module'),cpp_module=request.get('cpp_module'))!=program:
        raise ValueError('Source changed during search admission; start a fresh run')
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    runner=Runner(output,request.get('timeout_seconds',120));started=time.monotonic()
    name='source'+source.suffix
    request={**request,'source':name};save(output/'request.json',request);(output/name).write_bytes(original)
    save(output/'program.json',program.record())
    result={'schema':'numerics-run-v1','status':'unresolved','kind':'counterexample_search',
        'completed_stages':['source_admitted'],'source_path':str(source),'source_sha256':sha(output/name),
        'scope':'Untrusted CBMC positivity-witness proposal, followed by ordinary Lean witness certification.',
        'assumptions':['The search C harness is an unproved aid; only the independently reconstructed Lean violation certifies the frozen source model.']}
    try:
        from numerics.integrations.registry import Session
        session=Session(program,request,output,output/'.work',runner,None,name)
        session.evidence.pop('selected_producer',None)
        session.evidence['selected_witness_proposer']='cbmc';session.save()
        words=session.execute('cbmc','witness-proposer')
        child={k:v for k,v in request.items() if k not in ('counterexample_search','search_tools')}
        child.update(source=str(output/name),counterexample={'inputs':words,'output':request['counterexample_search']['output']})
        save(output/'witness-request.json',child)
        from numerics.workflow.counterexample import certify as check
        runner.last_stage='witness-check'
        checked=check(output/'witness-request.json',output/'witness-run')
        if checked['status']!='counterexample':
            result['candidate_result']={k:checked[k] for k in ('status','failure_stage','failure_kind') if k in checked}
            raise SearchUnresolved('candidate_rejected','CBMC proposed a witness but ordinary Lean/source checking rejected it; see witness-run/report.md')
        result.update(status='counterexample',entry_theorem=checked['entry_theorem'],
                      completed_stages=['source_admitted','witness_proposed','lean_root_checked','source_diagnostics_checked'],
                      outputs=checked['outputs'],assumptions=checked['assumptions'])
    except (RuntimeError,ValueError,OSError,ArithmeticError) as error:
        result.update(error=str(error),failure_stage=runner.last_stage,failure_kind=getattr(error,'kind','stage_rejected'))
        log=output/'runs'/runner.last_stage/'run.json'
        if log.is_file():
            status=json.loads(log.read_text())['status']
            if status=='timeout':result['failure_kind']='timeout'
            elif status=='launch_error':result['failure_kind']='missing_tool'
    finally:
        result['elapsed_seconds']=time.monotonic()-started
        (output/'report.md').write_text('# Counterexample search: '+result['status']+'\n\n'+result['scope']+'\n\n'+
            (result.get('error') or 'The final root is in witness-run/report.md; replay this parent run without CBMC.')+'\n')
        seal(output,result)
    return result


def replay(path,output,*,timeout_seconds=None):
    request,source,program,questions=prepare(path/'request.json',replay=True)
    original=json.loads((path/'result.json').read_text())
    if questions or original['status']!='counterexample':raise ValueError('No completed search counterexample to replay')
    child=json.loads((path/'witness-run/request.json').read_text())
    expected={k:v for k,v in request.items() if k not in ('counterexample_search','search_tools','source')}
    actual={k:v for k,v in child.items() if k not in ('counterexample','source')}
    if expected!=actual or (path/'witness-run'/child['source']).read_bytes()!=source.read_bytes():
        raise ValueError('Search witness changed the original source or requirement')
    if child['counterexample']['output']!=request['counterexample_search']['output']:
        raise ValueError('Search witness changed the selected output')
    from numerics.workflow.certification import replay_run
    return replay_run(path/'witness-run',output,timeout_seconds=timeout_seconds)
