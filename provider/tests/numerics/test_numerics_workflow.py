"""Workflow regressions, including optional fresh Lean checks and rejection controls."""
from fractions import Fraction as Q
from dataclasses import replace
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from numerics.analysis.bounds import analyze
from numerics.frontends.scalar import Unsupported, execute, parse, word
from numerics.workflow.certification import ROOT, Runner, audit_run, certify, replay_run, save, sha
from numerics.workflow.certification import output_bounds
from install_numerics_skill import install


class RustAdmissionTests(unittest.TestCase):
    def test_mutation_shadowing_and_order(self):
        source = ('pub fn f(x: f64, y: f64, z: f64) -> (f64, f64) {'
                  'let mut a = x + y; a += z; let x: f64 = -0.0; (a, x) }')
        self.assertEqual(tuple(map(word, execute(parse('rust', source, 'f'), (1e16, -1e16, 1.0)))),
                         (word(1.0), word(-0.0)))

    def test_unsupported_semantics_are_rejected(self):
        bodies = ['x.sin()', 'if x > 0.0 { x } else { -x }', '[x, x][0]',
                  'let a = x; a = x + 1.0; a', 'x + 1', 'x;',
                  'return x; x + x', 'x.mul_add(x, x)', '(x, x)']
        for body in bodies:
            with self.subTest(body=body), self.assertRaises(Unsupported):
                parse('rust', 'pub fn f(x: f64) -> f64 { '+body+' }', 'f')


class ProducerGapTests(unittest.TestCase):
    def test_fixed_grid_inflates_a_simple_roundoff_allowance(self):
        program=parse('python','def f(x, y):\n    return x + y\n','f')
        bounds, steps=analyze(program,{'x':['-1','1'],'y':['-1','1']})
        raw=Q(2)**(steps[0]['exponent']-52)
        self.assertEqual(bounds[program.outputs[0]].e/raw,64)

    def test_tiny_positive_divisor_loses_its_floor_without_changing_inputs(self):
        program=parse('python','def f(p, r):\n    return p / (p + r)\n','f')
        domain={x:['1/18014398509481984','1/9007199254740992'] for x in ('p','r')}
        with self.assertRaisesRegex(ValueError,'denominator'):
            analyze(program,domain)


class InstallationTests(unittest.TestCase):
    def test_skill_installation_is_repeatable_and_preserves_an_existing_skill(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            link=install(root)
            self.assertTrue((link/'SKILL.md').is_file())
            self.assertEqual(install(root),link)
            link.unlink();link.mkdir();(link/'SKILL.md').write_text('existing')
            with self.assertRaisesRegex(ValueError,'preserved'):
                install(root)
            self.assertEqual((link/'SKILL.md').read_text(),'existing')


class RunnerEnvironmentTests(unittest.TestCase):
    def test_cache_settings_remain_the_callers_choice(self):
        keys=['LAKE_ARTIFACT_CACHE','LAKE_RESTORE_ARTIFACTS','MATHLIB_NO_CACHE_ON_UPDATE']
        for selection in [None,['false','false','0']]:
            with self.subTest(selection=selection), tempfile.TemporaryDirectory() as directory, patch.dict(os.environ):
                for i,key in enumerate(keys):
                    if selection is None: os.environ.pop(key,None)
                    else: os.environ[key]=selection[i]
                root=Path(directory)
                code='import os,json;print(json.dumps([os.environ.get(k) for k in '+repr(keys)+']))'
                actual=Runner(root).run('environment',[sys.executable,'-c',code],cwd=root)
                self.assertEqual(json.loads(actual),selection or [None]*len(keys))


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1',
                     'Run make numerics-check for fresh Lean certification controls')
class LeanWorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.storage=tempfile.TemporaryDirectory(prefix='flare-workflows-')
        cls.root=Path(cls.storage.name)
        cls.source=cls.root/'input.py'
        cls.source.write_text('def f(x):\n    return x + x\n')
        cls.request={'schema':'numerics-request-v1','language':'python','source':'input.py',
            'function':'f','domain':{'x':['-1','1']},'specification':['2*x'],
            'outputs':[{'name':'sum','unit':'m','limit':'1/10000000000'}],'target':'lean'}
        save(cls.root/'request.json',cls.request)
        cls.baseline=cls.root/'baseline'
        result=certify(cls.root/'request.json',cls.baseline)
        if result['status']!='certified':
            raise AssertionError('Baseline setup failed: '+json.dumps(result))

    @classmethod
    def tearDownClass(cls):
        cls.storage.cleanup()

    def run_variant(self,name,**changes):
        request={**self.request,**changes}
        save(self.root/(name+'.json'),request)
        output=self.root/name
        return certify(self.root/(name+'.json'),output),output

    def clone(self,name):
        destination=self.root/name
        shutil.copytree(self.baseline,destination)
        return destination

    def reseal_file(self,run,name):
        path=run/'result.json'; result=json.loads(path.read_text())
        result['artifacts'][name]=sha(run/name); save(path,result)

    def test_saved_proof_replays_without_producer_or_runtime(self):
        with patch('numerics.workflow.certification.analyze',side_effect=AssertionError('producer called')), \
             patch('numerics.runtimes.source.admit_runtime',side_effect=AssertionError('runtime called')):
            result=replay_run(self.baseline,self.root/'replay')
        self.assertEqual((result['status'],result['certificate_status']),('replayed','certified'))

    def test_cli_from_a_separate_application_directory(self):
        script=ROOT/'scripts/certify_numerics.py'
        output=self.root/'external-cli'
        command=[sys.executable,str(script),'run','--request',str(self.root/'request.json'),
                 '--out',str(output)]
        run=subprocess.run(command,cwd=self.root,capture_output=True,text=True,timeout=120)
        self.assertEqual(run.returncode,0,run.stdout+run.stderr)
        self.assertEqual(json.loads(run.stdout)['status'],'certified')

    def test_wrong_independent_specification_fails_in_lean(self):
        result,run=self.run_variant('wrong-spec',specification=['3*x'])
        self.assertEqual(result['status'],'unresolved')
        self.assertEqual(result['failure_stage'],'lean-proof')
        self.assertNotIn('lean_root_checked',result['completed_stages'])
        self.assertIn('unsolved goals',(run/'runs/lean-proof/stdout.txt').read_text())

    def test_budget_failure_retains_a_checked_allowance(self):
        result,_=self.run_variant('tight',outputs=[{'name':'sum','unit':'m','limit':'1/1000000000000000000'}])
        self.assertEqual(result['status'],'budget_not_met')
        self.assertIn('lean_root_checked',result['completed_stages'])
        self.assertEqual(result['outputs'][0]['evidence'],'checked')

    def test_false_zero_error_proposal_is_rejected_in_lean(self):
        source=self.root/'addition.py';source.write_text('def f(x, y):\n    return x + y\n')
        # This addition rounds to 1 although its exact original-input sum is larger.
        self.assertEqual(1.0+2.0**-54,1.0)
        self.assertGreater(Q(1)+Q(2)**-54,Q(1))
        def invalid_proposal(program,request):
            bounds,steps=output_bounds(program,request)
            node=program.outputs[0];bounds[node]=replace(bounds[node],e=Q(0))
            return bounds,steps
        with patch('numerics.workflow.certification.output_bounds',side_effect=invalid_proposal):
            result,run=self.run_variant('false-bound',source='addition.py',
                domain={'x':['-1','1'],'y':['-1','1']},specification=['x+y'])
        self.assertEqual(result['status'],'unresolved')
        self.assertEqual(result['failure_stage'],'lean-proof')
        self.assertNotIn('accepted_bounds',json.loads((run/'analysis.json').read_text()))

    def test_runtime_disagreement_does_not_certify_a_valid_model_proof(self):
        def wrong_words(program,source,cases,*args):
            return [(word(1.0),) for _ in cases]
        with patch('numerics.runtimes.diagnostics.source_results',side_effect=wrong_words):
            result,_=self.run_variant('wrong-runtime')
        self.assertEqual(result['status'],'unresolved')
        self.assertIn('lean_root_checked',result['completed_stages'])
        self.assertNotIn('source_diagnostics_checked',result['completed_stages'])
        self.assertEqual(result['failure_stage'],'source-diagnostics')
        self.assertIn('source runtime and extracted graph differ',result['error'])

    def test_artifact_hash_and_original_source_freshness(self):
        run=self.clone('altered-artifact')
        (run/'lean/Workflow/Proof.lean').write_text('-- altered\n')
        with self.assertRaisesRegex(ValueError,'artifact'):
            audit_run(run,True)
        run=self.clone('stale-source'); other=self.root/'changed.py'
        other.write_text('def f(x):\n    return x\n')
        path=run/'result.json'; result=json.loads(path.read_text())
        result['source_path']=str(other);save(path,result)
        with self.assertRaisesRegex(ValueError,'Original source changed'):
            audit_run(run)
        self.assertEqual(audit_run(run,True)['status'],'fresh')

    def test_resealed_kernel_is_checked_against_original_source(self):
        run=self.clone('wrong-kernel'); name='lean/Workflow/Kernel.lean'
        path=run/name;path.write_text(path.read_text().replace('(a0 + a0)','(a0 - a0)'))
        self.reseal_file(run,name)
        with self.assertRaisesRegex(ValueError,'does not match'):
            replay_run(run,self.root/'wrong-kernel-replay')

    def test_root_check_cannot_be_removed_with_inline_audit(self):
        run=self.clone('missing-root'); name='lean/Workflow/Proof.lean'
        path=run/name; text=path.read_text().split('\nopen Lean in\nrun_cmd do')[0]
        path.write_text(text.replace('theorem certificate ','theorem omitted_certificate '))
        self.reseal_file(run,name)
        output=self.root/'missing-root-replay'
        with self.assertRaisesRegex(RuntimeError,'lean-root-check'):
            replay_run(run,output)
        self.assertIn('certificate',(output/'runs/lean-root-check/stdout.txt').read_text())

    def test_authored_proof_and_untrusted_axiom_control(self):
        source=self.root/'identity.py';source.write_text('def f(x):\n    return x\n')
        authored=self.root/'Identity.lean'
        signature='''(a0 : Float)
    (h0 : a0.isFinite = true ∧ (-1 : ℝ) ≤ Flare.Binary64.Value.value a0 ∧
      Flare.Binary64.Value.value a0 ≤ (1 : ℝ)) :
    (Workflow.kernel a0).isFinite = true ∧
      |Flare.Binary64.Value.value (Workflow.kernel a0) - Workflow.reference
        (Flare.Binary64.Value.value a0)| ≤ (0 : ℝ)'''
        header='module\npublic import Workflow.Kernel\n@[expose] public section\n'
        authored.write_text(header+'theorem identity_accuracy '+signature+''' := by
  exact ⟨h0.1, by simp [Workflow.kernel, Workflow.reference]⟩
''')
        changes={'source':'identity.py','specification':['x'],
                 'proof':{'source':'Identity.lean','accuracy':'identity_accuracy','bounds':['0']}}
        result,run=self.run_variant('authored',**changes)
        self.assertEqual(result['status'],'certified',result.get('error'))
        self.assertEqual(result['outputs'][0]['bound'],'0')
        authored.write_text(header+'axiom identity_accuracy '+signature+'\n')
        with self.assertRaisesRegex(ValueError,'Authored proof source changed'):
            audit_run(run)
        result,run=self.run_variant('axiom',**changes)
        self.assertEqual(result['status'],'unresolved')
        self.assertIn('Unexpected axiom',(run/'runs/lean-proof/stdout.txt').read_text())

    def loop_request(self):
        path=self.root/'loop.py'
        path.write_text('''def step(x, previous, observation):
    return (x + observation) / 2.0, observation
def run(x, y, z):
    previous = y
    for observation in (y, z):
        x, previous = step(x, previous, observation)
    return x, previous
''')
        return {'source':'loop.py','function':'run','domain':{x:['-1','1'] for x in ['x','y','z']},
                'outputs':[{'name':x,'unit':'m','limit':'1/10000000000'} for x in ['state','last']],
                'specification':{'kind':'fold','initial':['x','y'],'sequence':['y','z'],
                                 'state':['state','last'],'element':'observation',
                                 'step':['(state + observation) / 2','observation']}}

    def test_bounded_loop_certificate_replays_against_the_exact_recurrence(self):
        result,run=self.run_variant('loop',**self.loop_request())
        self.assertEqual(result['status'],'certified',result.get('error'))
        self.assertEqual(replay_run(run,self.root/'loop-replay')['status'],'replayed')

    def test_reversed_loop_recurrence_is_rejected_in_lean(self):
        request=self.loop_request();request['specification']['sequence']=['z','y']
        result,run=self.run_variant('wrong-loop',**request)
        self.assertEqual(result['status'],'unresolved')
        self.assertEqual(result['failure_stage'],'lean-proof')
        self.assertIn('rfl',(run/'runs/lean-proof/stdout.txt').read_text())


if __name__=='__main__': unittest.main()
