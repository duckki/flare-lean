"""Helper contracts, accumulated-error wiring, cache reuse and frozen replay."""
from dataclasses import replace
from fractions import Fraction as Q
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from numerics.analysis import composition
from numerics.analysis.bounds import analyze, scale_normalized
from numerics.frontends.scalar import execute, parse, word
from numerics.integrations.registry import Session
from numerics.workflow.proof_cache import ProofCache
from numerics.workflow.certification import ROOT, certify, prepare, replay_run, save, sha


SOURCE = '''def advance(x, y, z):
    return (x + z) / 2.0, (y + z) / 2.0
def run2(x, y, z0, z1):
    for z in (z0, z1):
        x, y = advance(x, y, z)
    return x, y
def run4(x, y, z0, z1, z2, z3):
    for z in (z0, z1, z2, z3):
        x, y = advance(x, y, z)
    return x, y
'''


def request(count=2):
    return {'schema':'numerics-request-v1','source':'source.py','language':'python','function':'run'+str(count),
            'domain':{name:['-1','1'] for name in ['x','y',*['z'+str(i) for i in range(count)]]},
            'outputs':[{'name':name,'unit':'m','limit':'1/1000000'} for name in ['x','y']],
            'specification':{'kind':'fold','initial':['x','y'],'state':['m','p'],'element':'z',
                             'sequence':['z'+str(i) for i in range(count)],
                             'step':['(m+z)/2','(p+z)/2']}}


class CompositionTests(unittest.TestCase):
    def test_helper_layout_retains_word_semantics_and_one_shared_function(self):
        r = request(4); program = parse('python', SOURCE, r['function'])
        calls = composition.groups(program, SOURCE, r)
        self.assertEqual([call['function'] for call in calls], ['advance']*4)
        for values in [(1.,-1.,.5,-.5,.25,-.25), (-0.,0.,-0.,0.,-0.,0.)]:
            env = {'a'+str(i):x for i,x in enumerate(values)}
            for call in calls:
                local, _, inputs = composition.local_program(program, call)
                results = execute(local, [env[name] for name in inputs])
                env.update(zip(call['outputs'],results,strict=True))
            self.assertEqual([word(env[name]) for name in program.outputs],
                             [word(value) for value in execute(program, values)])
        value = composition.proposal(program, r, calls)
        self.assertEqual(value.details['function_count'], 1)

    def test_scale_aware_analysis_reaches_128_without_changing_the_contract(self):
        r, _, program, _ = prepare(ROOT/'examples/numerics/scale/kalman_128.json')
        bounds, steps = analyze(program, r['domain'], scale_normalized)
        self.assertEqual([target['limit'] for target in r['outputs']], ['1/10000','1/1000000'])
        self.assertTrue(all(bound.e >= 0 for bound in bounds.values()))
        self.assertGreater(bounds[program.outputs[0]].e, Q(r['outputs'][0]['limit']))
        self.assertEqual(len(steps), len(program.nodes))

    def test_corrupted_compiled_cache_is_a_miss(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); source = root/'Module.lean';source.write_text('module\n')
            target = root/'Module.olean'
            for suffix in ['', '.private', '.server']:
                Path(str(target)+suffix).write_bytes(b'compiled-'+suffix.encode())
            cache = ProofCache(root/'pool', {'lean-toolchain':'test'})
            cache.save(source,target)
            restored = root/'Restored.olean'
            self.assertTrue(cache.restore(source,restored))
            entry = next((root/'pool').iterdir());(entry/'module.olean').write_bytes(b'changed')
            self.assertFalse(cache.restore(source,restored))
            source.write_text('module\n-- different source\n')
            self.assertFalse(cache.restore(source,restored))


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION') == '1', 'Run make numerics-check')
class CompositionLeanTests(unittest.TestCase):
    def test_changed_caller_reuses_prefix_contracts_and_replay_compiles_without_cache(self):
        with tempfile.TemporaryDirectory(prefix='flare-contracts-') as directory:
            root = Path(directory);(root/'source.py').write_text(SOURCE)
            for count in [2,4]:
                r = {**request(count),'contract_cache':str(root/'pool')}
                if count == 4:
                    r['domain']['z3'] = ['-1/2','1/2']
                save(root/'request.json',r)
                result = certify(root/'request.json',root/str(count))
                self.assertEqual(result['status'],'certified',result.get('error'))
            reuse = json.loads((root/'4/proof-reuse.json').read_text())['modules']
            self.assertGreaterEqual(sum(item['reused'] for item in reuse), 3)
            with patch.object(Session,'execute',side_effect=AssertionError('producer called')), \
                 patch('numerics.analysis.composition.proposal',side_effect=AssertionError('inference called')):
                result = replay_run(root/'4',root/'replay')
            self.assertEqual(result['status'],'replayed')
            replayed = json.loads((root/'replay/proof-reuse.json').read_text())
            self.assertFalse(replayed['cache_enabled'])
            self.assertTrue(all(not item['reused'] for item in replayed['modules']))
            copied = root/'changed-function';shutil.copytree(root/'4',copied)
            function = next((copied/'lean/Workflow/Functions').glob('*.lean'))
            function.write_text(function.read_text().replace('(a0 + a1)','(a0 - a1)',1))
            recorded = json.loads((copied/'result.json').read_text())
            recorded['artifacts'][str(function.relative_to(copied))] = sha(function)
            save(copied/'result.json',recorded)
            with self.assertRaisesRegex(ValueError,'helper function does not match'):
                replay_run(copied,root/'wrong-function-replay')
            # Rehashing metadata does not let a changed layout attach to frozen source.
            path = root/'4/model-layout.json'; layout = json.loads(path.read_text())
            layout['calls'][0]['start'] = 1;save(path,layout)
            path = root/'4/result.json'; recorded = json.loads(path.read_text())
            recorded['artifacts']['model-layout.json'] = sha(root/'4/model-layout.json');save(path,recorded)
            with self.assertRaisesRegex(ValueError,'does not match'):
                replay_run(root/'4',root/'wrong-layout')

    def test_wrong_recurrence_and_reset_incoming_error_are_rejected(self):
        with tempfile.TemporaryDirectory(prefix='flare-contract-rejection-') as directory:
            root = Path(directory);(root/'source.py').write_text(SOURCE)
            r = request();r['specification']['step'][0] = '(m+z)/3'
            save(root/'request.json',r)
            result = certify(root/'request.json',root/'wrong-recurrence')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
            save(root/'request.json',request())
            original = composition.contract_module
            def reset(local, bounds, steps, function_key, key):
                changed = {name:replace(bound,e=Q(0)) if name.startswith('a') else bound
                           for name,bound in bounds.items()}
                return original(local,changed,steps,function_key,key)
            with patch('numerics.analysis.composition.contract_module',side_effect=reset):
                result = certify(root/'request.json',root/'reset-error')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
            self.assertNotIn('lean_root_checked',result['completed_stages'])


if __name__ == '__main__':
    unittest.main()
