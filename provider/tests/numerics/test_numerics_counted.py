"""Compact counted-source proofs, nonzero incoming error, reuse and large graphs."""
from dataclasses import replace
from fractions import Fraction as Q
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from numerics.analysis import counted
from numerics.analysis.bounds import analyze, scale_normalized
from numerics.frontends.scalar import Unsupported, execute, parse, word
from numerics.integrations.registry import Session
from numerics.frontends.python_counted import load_counted
from numerics.workflow.certification import ROOT, certify, prepare, replay_run, save, sha


EXAMPLES=ROOT/'examples/numerics/counted'


class CountedSourceTests(unittest.TestCase):
    def test_real_loop_count_binding_and_simultaneous_updates_match_words(self):
        source=('def step(other, bias, state):\n    return (state+bias)/2.0, (other-bias)/2.0\n'
                'def run(count: int, x: float, y: float, z: float):\n'
                '    for index in range(count):\n        x, y = step(y,z,x)\n    return x,y\n')
        for count in [0,1,16,1024]:
            p=parse('python',source,'run',python_counted={'parameter':'count','iterations':count})
            function=load_counted(source,p)
            for args in [(1.,-1.,.25),(-0.,0.,-0.),(2**-1022,-2**-1022,2**-1074)]:
                self.assertEqual(tuple(map(word,execute(p,args))),tuple(map(word,function(*args))))
            self.assertEqual(len(p.nodes),6)

    def test_graph_modules_and_parametric_proof_do_not_expand_with_horizon(self):
        proofs=[]; modules=[]
        for count in [1,16,128,1024]:
            r,_,p,q=prepare(EXAMPLES/f'smoothing_{count:04}.json')
            self.assertFalse(q)
            value=counted.proposal(p,r)
            modules.append(value.modules)
            proofs.append(value.lean_source.split('theorem accuracy',1)[0])
            self.assertEqual(value.details['contract_count'],1)
            self.assertEqual(len(p.nodes),6)
        self.assertTrue(all(m==modules[0] for m in modules))
        self.assertEqual(len(set(proofs)),1)

    def test_incoming_state_errors_are_part_of_the_step_contract(self):
        r,_,p,_=prepare(EXAMPLES/'smoothing_0001.json')
        inputs=counted.proposed_inputs(p,r)
        bounds,_=analyze(counted.local_program(p),r['domain'],scale_normalized,input_bounds=inputs)
        for name in p.outputs:
            self.assertGreaterEqual(bounds[name].e,Q(r['outputs'][0]['limit'])/2)
            self.assertLess(bounds[name].e,Q(r['outputs'][0]['limit']))

    def test_counted_admission_rejects_ambiguous_or_unmodelled_execution(self):
        source=(EXAMPLES/'smoothing.py').read_text()
        selected={'parameter':'steps','iterations':16}
        for selection in [False,{}, {'parameter':'steps','iterations':True},
                          {'parameter':'steps','iterations':-1}, {'parameter':'steps','iterations':65537}]:
            with self.subTest(selection=selection),self.assertRaises(Unsupported):
                parse('python',source,'smooth',python_counted=selection)
        changes=[('range(steps)','range(steps+1)'),('range(steps)','range(1,steps)'),
                 ('x, y = smooth_step(x, y, observation)','x, y = smooth_step(x, x, observation)'),
                 ('return x, y\n','return y, x\n'),('for _ in range','for x in range'),
                 ('steps: int','steps: float'),('    for _ in range','    print(x)\n    for _ in range')]
        for old,new in changes:
            with self.subTest(old=old),self.assertRaises(Unsupported):
                parse('python',source.replace(old,new),'smooth',python_counted=selected)
        with self.assertRaises(Unsupported):
            parse('python',source,'smooth',python_counted=selected,python_branches=True)


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1','Run make numerics-check')
class CountedLeanTests(unittest.TestCase):
    def setUp(self):
        self.parent=ROOT/'.cache/numerics-generated';self.parent.mkdir(parents=True,exist_ok=True)

    def request(self,root,example,**updates):
        r,source,_,_=prepare(EXAMPLES/example)
        save(root/'request.json',{**r,'source':str(source),**updates})
        return root/'request.json'

    def test_all_horizons_and_second_family_replay_without_producers_or_reuse(self):
        with tempfile.TemporaryDirectory(prefix='counted-',dir=self.parent) as directory:
            root=Path(directory)
            for count in [1,16,128,1024]:
                request=self.request(root,f'smoothing_{count:04}.json',contract_cache=str(root/'pool'))
                result=certify(request,root/str(count))
                self.assertEqual(result['status'],'certified',result.get('error'))
                self.assertEqual(result['producer_validation'],'lean-counted-invariant-v1')
            reuse=json.loads((root/'1024/proof-reuse.json').read_text())
            self.assertTrue(all(x['reused'] for x in reuse['modules']))
            result=certify(self.request(root,'decay_1024.json'),root/'decay')
            self.assertEqual(result['status'],'certified',result.get('error'))
            for name in ['1024','decay']:
                with patch.object(Session,'execute',side_effect=AssertionError('producer called')), \
                     patch('numerics.analysis.counted.proposal',side_effect=AssertionError('invariant inference called')):
                    self.assertEqual(replay_run(root/name,root/(name+'-replay'))['status'],'replayed')
                reuse=json.loads((root/(name+'-replay')/'proof-reuse.json').read_text())
                self.assertFalse(reuse['cache_enabled'])
                self.assertTrue(all(not x['reused'] for x in reuse['modules']))

    def test_wrong_recurrence_zero_incoming_error_and_resealed_model_fail(self):
        with tempfile.TemporaryDirectory(prefix='counted-negative-',dir=self.parent) as directory:
            root=Path(directory)
            r,_,_,_=prepare(EXAMPLES/'smoothing_0016.json')
            wrong={**r['specification'],'step':['(m+observation)/3','(p+observation)/2']}
            result=certify(self.request(root,'smoothing_0016.json',specification=wrong),root/'wrong-step')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
            original=counted.proposed_inputs
            def zero(p,r):
                return {name:replace(b,e=Q(0)) for name,b in original(p,r).items()}
            with patch('numerics.analysis.counted.proposed_inputs',side_effect=zero):
                result=certify(self.request(root,'smoothing_0016.json'),root/'zero-error')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
            run=root/'valid';self.assertEqual(certify(self.request(root,'smoothing_0016.json'),run)['status'],'certified')
            module=next((run/'lean/Workflow/Functions').glob('*.lean'))
            module.write_text(module.read_text().replace('(a0 + a2)','(a0 - a2)',1))
            recorded=json.loads((run/'result.json').read_text())
            recorded['artifacts'][str(module.relative_to(run))]=sha(module);save(run/'result.json',recorded)
            with self.assertRaisesRegex(ValueError,'counted helper does not match'):
                replay_run(run,root/'wrong-model')

    def test_large_source_graph_caller_reuse_and_cold_replay(self):
        with tempfile.TemporaryDirectory(prefix='large-shared-',dir=self.parent) as directory:
            root=Path(directory)
            for count in [32,64]:
                r,source,p,_=prepare(ROOT/'examples/numerics/scale'/f'shared_{count:04}.json')
                save(root/'request.json',{**r,'source':str(source),'contract_cache':str(root/'pool')})
                result=certify(root/'request.json',root/str(count))
                self.assertEqual(result['status'],'certified',result.get('error'))
            self.assertEqual(sum(n.op!='constant' for n in p.nodes),1024)
            reuse=json.loads((root/'64/proof-reuse.json').read_text())['modules']
            self.assertTrue(all(m['reused'] for m in reuse))
            with patch.object(Session,'execute',side_effect=AssertionError('producer called')):
                self.assertEqual(replay_run(root/'64',root/'cold-replay')['status'],'replayed')


if __name__=='__main__':
    unittest.main()
