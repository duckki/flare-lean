"""First-class witness delivery: real violations, independent roots and cold replay."""
from fractions import Fraction as Q
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from numerics.workflow.counterexample import ENTRY, exact_expression, propose, terms
from numerics.frontends.scalar import Unsupported
from numerics.integrations.registry import ToolError
from numerics.workflow.certification import ROOT, audit_run, certify, prepare, replay_run, save, sha


FIXTURES = ROOT/'examples/numerics/counterexamples'


class WitnessAdmissionTests(unittest.TestCase):
    def test_exact_reference_uses_decimal_rationals_not_host_rounding(self):
        self.assertEqual(exact_expression('x + 0.1', {'x': Q(1, 3)}), Q(13, 30))
        with self.assertRaisesRegex(ValueError, 'zero denominator'):
            exact_expression('x / (x-x)', {'x': Q(1)})
        with self.assertRaises(Unsupported):
            exact_expression('__import__("os")', {})

    def test_admits_explicit_witness_without_bound_inference(self):
        for name in ['naive_covariance', 'cancellation']:
            request, _, program, questions = prepare(FIXTURES/(name+'.json'))
            self.assertFalse(questions)
            record = propose(program, request)
            self.assertEqual(record['outputs'], ['0x0000000000000000'])
            terms(program, request, record)

    def test_rejects_ambiguous_nonfinite_and_unbridged_witness_requests(self):
        original = json.loads((FIXTURES/'naive_covariance.json').read_text())
        original['source'] = str(ROOT/'examples/numerics/counterexamples/naive_covariance.py')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'request.json'
            for selection in [None, {}, {'inputs':{}, 'output':0},
                    {'inputs':{'p':'1.0','r':'0x3c90000000000000'},'output':0},
                    {'inputs':{'p':'0x7ff0000000000000','r':'0x3c90000000000000'},'output':0},
                    {**original['counterexample'], 'output':True}]:
                with self.subTest(selection=selection), self.assertRaises(ValueError):
                    save(path,{**original,'counterexample':selection}); prepare(path)
            for change in [{'producer':'gappa'}, {'target':'rust-aeneas'}, {'proof':{'source':'x'}},
                           {'analysis_tools':{'cbmc':{}}}, {'rust_application':{}}]:
                with self.subTest(change=change), self.assertRaises(Unsupported):
                    save(path,{**original,**change}); prepare(path)
            invalid = {**original,'outputs':[{'name':'p','unit':'m²','property':'strict_positive','limit':'1'}]}
            save(path,invalid)
            with self.assertRaisesRegex(ValueError, 'no error limit'): prepare(path)
            invalid.pop('counterexample'); invalid['outputs'][0].pop('limit')
            save(path,invalid)
            with self.assertRaisesRegex(Unsupported, 'witness route'): prepare(path)
            incomplete = {k:v for k,v in original.items() if k != 'specification'}
            save(path,incomplete)
            self.assertIn('specification',[q['field'] for q in prepare(path)[-1]])


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION') == '1',
                     'Run make numerics-check for independent Lean witness checks')
class WitnessWorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.storage = tempfile.TemporaryDirectory(prefix='flare-witnesses-')
        cls.root = Path(cls.storage.name)
        cls.baseline = cls.root/'baseline'
        result = certify(FIXTURES/'naive_covariance.json',cls.baseline)
        if result['status'] != 'counterexample':
            proof = cls.baseline/'runs/lean-proof/stdout.txt'
            raise AssertionError(proof.read_text() if proof.exists() else result.get('error'))

    @classmethod
    def tearDownClass(cls): cls.storage.cleanup()

    def variant(self, name, **changes):
        request = json.loads((FIXTURES/'naive_covariance.json').read_text())
        request['source'] = str(ROOT/'examples/numerics/counterexamples/naive_covariance.py')
        request.update(changes); save(self.root/(name+'.json'),request)
        return certify(self.root/(name+'.json'),self.root/name)

    def clone(self, name):
        path = self.root/name; shutil.copytree(self.baseline,path); return path

    def reseal(self, path, name):
        result = json.loads((path/'result.json').read_text())
        result['artifacts'][name] = sha(path/name); save(path/'result.json',result)

    def test_proved_violation_and_cold_replay_need_no_search_runtime_or_producer(self):
        result = json.loads((self.baseline/'result.json').read_text())
        self.assertEqual(result['entry_theorem'],ENTRY)
        self.assertEqual(result['outputs'][0]['reference'],'1/18014398509481985')
        self.assertEqual(result['outputs'][0]['evidence'],'checked')
        self.assertEqual(audit_run(self.baseline)['status'],'fresh')
        with (patch('numerics.workflow.counterexample.propose',side_effect=AssertionError('witness search')),
             patch('numerics.workflow.counterexample.execute',side_effect=AssertionError('model execution')),
             patch('numerics.runtimes.source.admit_runtime',side_effect=AssertionError('runtime')),
             patch('numerics.runtimes.source.source_results',side_effect=AssertionError('source execution')),
             patch('numerics.integrations.registry.adapters',side_effect=AssertionError('producer'))):
            replay = replay_run(self.baseline,self.root/'cold-replay')
        self.assertEqual((replay['status'],replay['certificate_status']),('replayed','counterexample'))

    def test_absolute_error_violation_and_satisfying_witness_remain_distinct(self):
        result = certify(FIXTURES/'cancellation.json',self.root/'error-violation')
        self.assertEqual(result['status'],'counterexample',result.get('error'))
        self.assertEqual(result['outputs'][0]['absolute_error'],'1/18014398509481984')
        result = self.variant('satisfies',outputs=[{'name':'variance','unit':'m²','limit':'1'}])
        self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-proof'))
        self.assertNotIn('lean_root_checked',result['completed_stages'])
        source = self.root/'negative-pair.py'
        source.write_text('def residual(x,y):\n    return x, (x+y)-x\n')
        request = json.loads((FIXTURES/'cancellation.json').read_text())
        request.update(source=str(source),domain={'x':['-2','-1'],
            'y':['-1/9007199254740992','-1/18014398509481984']},specification=['x','y'],
            outputs=[{'name':'input','unit':'m','limit':'1'},request['outputs'][0]],
            counterexample={'inputs':{'x':'0xbff0000000000000','y':'0xbc90000000000000'},'output':1})
        save(self.root/'negative.json',request)
        result = certify(self.root/'negative.json',self.root/'negative-pair')
        self.assertEqual(result['status'],'counterexample',result.get('error'))
        self.assertEqual(result['outputs'][0]['value'],'-1')

    def test_domain_and_exact_positive_reference_are_checked_in_lean(self):
        result = self.variant('out-of-domain',domain={'p':['3','4'],'r':['0','1']})
        self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-proof'))
        result = self.variant('nonpositive-reference',specification=['0'])
        self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-proof'))

    def test_pairs_signed_zero_and_smallest_subnormal(self):
        source = self.root/'pair.py'; source.write_text('def f(x,y):\n    return -x, y-y\n')
        result = self.variant('pair',source=str(source),function='f',domain={'x':['0','0'],'y':[str(Q(2)**-1074)]*2},
            specification=['-x','y'],outputs=[{'name':'zero','unit':'m','property':'strict_positive'},
                                            {'name':'residual','unit':'m','property':'strict_positive'}],
            counterexample={'inputs':{'x':'0x0000000000000000','y':'0x0000000000000001'},'output':1})
        self.assertEqual(result['status'],'counterexample',result.get('error'))
        self.assertEqual(result['outputs'][0]['bits'],'0x8000000000000000')
        self.assertEqual(replay_run(self.root/'pair',self.root/'pair-replay')['status'],'replayed')
        path = self.root/'pair'
        record = json.loads((path/'witness.json').read_text()); record['reference'][0] = '1'
        save(path/'witness.json',record); self.reseal(path,'witness.json')
        with self.assertRaisesRegex(RuntimeError,'lean-root-check'):
            replay_run(path,self.root/'pair-false-other-reference')

    @unittest.skipUnless(shutil.which('rustc'), 'Requires original Rust source execution')
    def test_original_rust_source_and_cold_replay(self):
        source = self.root/'residual.rs'
        source.write_text('pub fn residual(x: f64, y: f64) -> f64 { (x + y) - x }\n')
        request = json.loads((FIXTURES/'cancellation.json').read_text())
        request.update(source=str(source),language='rust')
        save(self.root/'rust.json',request)
        result = certify(self.root/'rust.json',self.root/'rust')
        self.assertEqual(result['status'],'counterexample',result.get('error'))
        self.assertEqual(replay_run(self.root/'rust',self.root/'rust-replay')['status'],'replayed')

    def test_resealed_false_output_reference_and_changed_requirement_are_rejected(self):
        for name, changes in [('false-output',{'outputs':['0x3ff0000000000000']}),
                              ('false-reference',{'reference':['1']})]:
            path = self.clone(name); record = json.loads((path/'witness.json').read_text())
            record.update(changes); save(path/'witness.json',record); self.reseal(path,'witness.json')
            with self.subTest(name=name), self.assertRaisesRegex(RuntimeError,'lean-root-check'):
                replay_run(path,self.root/(name+'-replay'))
        path = self.clone('changed-domain'); request = json.loads((path/'request.json').read_text())
        request['domain']['p'] = ['3','4']; save(path/'request.json',request); self.reseal(path,'request.json')
        with self.assertRaisesRegex(RuntimeError,'lean-root-check'):
            replay_run(path,self.root/'changed-domain-replay')
        path = self.clone('changed-requirement'); request = json.loads((path/'request.json').read_text())
        request['outputs'] = [{'name':'variance','unit':'m²','limit':'1'}]
        save(path/'request.json',request); self.reseal(path,'request.json')
        with self.assertRaisesRegex(RuntimeError,'lean-root-check'):
            replay_run(path,self.root/'changed-requirement-replay')

    def test_removed_root_untrusted_axiom_and_overwritten_check_are_rejected(self):
        path = self.clone('missing-root'); proof = path/'lean/Workflow/Proof.lean'
        proof.write_text(proof.read_text().replace('theorem counterexample :','theorem omitted :'))
        self.reseal(path,'lean/Workflow/Proof.lean')
        with self.assertRaisesRegex(RuntimeError,'lean-root-check'):
            replay_run(path,self.root/'missing-root-replay')
        path = self.clone('axiom'); proof = path/'lean/Workflow/Proof.lean'
        text = proof.read_text(); start = text.index('theorem counterexample :')
        signature = text[start:].split(' := by')[0].replace('theorem counterexample','axiom counterexample')
        proof.write_text(text[:start]+signature+'\nend Workflow.Counterexample\n')
        self.reseal(path,'lean/Workflow/Proof.lean')
        (path/'lean/Workflow/Check.lean').write_text('-- no audit\n'); self.reseal(path,'lean/Workflow/Check.lean')
        with self.assertRaisesRegex(RuntimeError,'lean-root-check'):
            replay_run(path,self.root/'axiom-replay')
        self.assertIn('Unexpected axiom',(self.root/'axiom-replay/runs/lean-root-check/stdout.txt').read_text())

    def test_wrong_source_kernel_runtime_disagreement_and_missing_tool(self):
        path = self.clone('kernel'); proof = path/'lean/Workflow/Kernel.lean'
        proof.write_text(proof.read_text().replace('(a0 + a1)','(a0 - a1)'))
        self.reseal(path,'lean/Workflow/Kernel.lean')
        with self.assertRaisesRegex(ValueError,'does not match'):
            replay_run(path,self.root/'kernel-replay')
        with patch('numerics.runtimes.source.source_results',return_value=[(1,)]):
            result = self.variant('runtime-disagreement')
        self.assertEqual((result['status'],result['failure_stage']),('unresolved','source-diagnostics'))
        with patch('numerics.runtimes.source.admit_runtime',side_effect=ToolError('missing_tool','Missing source runtime')):
            result = self.variant('missing-runtime')
        self.assertEqual(result['status'],'unresolved')
        self.assertEqual(result['failure_stage'],'source-runtime-admission')
        self.assertEqual(result['failure_kind'],'missing_tool')
        with self.assertRaisesRegex(ValueError,'no completed counterexample'):
            replay_run(self.root/'missing-runtime',self.root/'missing-runtime-replay')
