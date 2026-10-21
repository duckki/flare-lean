"""Benchmark-only analysis of frozen models; this never produces a certificate."""
import argparse
import gzip
import json
from pathlib import Path
import time

from .analysis import analyze
from .graph import Graph,number
from .workflow import sha


def load_graph(path,outputs):
    path=Path(path)
    data=json.loads(gzip.decompress(path.read_bytes()))
    inputs=data['inputs'];nodes=data['nodes']
    if not isinstance(inputs,dict) or not isinstance(nodes,list) or len(nodes)>20000:
        raise ValueError('Unsupported frozen graph size or shape')
    variables=[name for name,entry in inputs.items() if entry['variable']]
    graph=Graph('frozen-model','pipeline',variables)
    domain={name:[inputs[name]['lower'],inputs[name]['upper']] for name in variables}
    for name,entry in inputs.items():
        if not entry['variable']: graph.names[name]=graph.literal(number(int(entry['word'])))
    origins={}
    for node in nodes:
        name=node['name'];op=node['op'];args=node['args']
        if name in graph.names or op not in ['+','-','*','/','neg'] or len(args)!=(1 if op=='neg' else 2):
            raise ValueError('Unsupported node or redefinition: '+name)
        values=[graph.names[x] for x in args]
        value=graph.unary('neg',values[0]) if op=='neg' else graph.binary({'+':'add','-':'sub','*':'mul','/':'div'}[op],*values)
        graph.names[name]=value
        origins[value.ref]={'node':name,'stage':node['stage']}
    program=graph.finish([graph.names[data['outputs'][name]] for name in outputs])
    metrics={'graph_nodes':len(program.nodes),'arithmetic_operations':len(nodes),
             'original_scalar_inputs':len(variables),'fixed_words':len(inputs)-len(variables),
             'stages':len({node['stage'] for node in nodes})}
    return program,domain,origins,metrics


def probe(path,outputs):
    started=time.monotonic()
    program,domain,origins,metrics=load_graph(path,outputs)
    result={'schema':'numerics-graph-probe-v1','status':'unresolved','metrics':metrics,
            'source_sha256':sha(path),'failure_stage':'analysis','entry_theorem':None,
            'producer_sha256':sha(Path(__file__).with_name('analysis.py')),
            'qualification':'Untrusted analysis of a manually exported arithmetic model. No Lean proof, source bridge, gate or complete application certificate is supplied.'}
    try:
        bounds,_=analyze(program,domain)
        result['status']='candidate_only';result.pop('failure_stage')
        result['outputs']=[{'name':name,'candidate_bound':str(bounds[node].e)}
                           for name,node in zip(outputs,program.outputs,strict=True)]
    except ValueError as error:
        result['error']=str(error)
        result['failure_origin']=origins.get(str(error).split(':',1)[0])
    result['seconds']=time.monotonic()-started
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--graph',type=Path,required=True)
    parser.add_argument('--outputs',nargs='+',required=True)
    args=parser.parse_args()
    print(json.dumps(probe(args.graph,args.outputs),indent=2))


if __name__=='__main__': main()
