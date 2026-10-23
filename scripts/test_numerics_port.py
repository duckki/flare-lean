"""Explicit Rust ports must be frozen, fresh and connected by checked Lean proof."""
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from numerics.workflow import prepare, save, sha, audit_run, replay_run, certify
from numerics.emit import kernel_source
from numerics.rust import extract

ROOT = Path(__file__).resolve().parents[1]

class ExplicitPortTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.request = json.loads((ROOT/'examples/numerics/mean_update.json').read_text())
        self.request['source'] = str((ROOT/'examples/numerics'/self.request['source']).resolve())
        self.request['target'] = 'rust-aeneas'
        (self.root/'port.rs').write_text('pub fn port(x: f64) -> f64 { x }')
        (self.root/'equiv.lean').write_text('-- test proof asset')
        self.request['rust_port'] = {'source':'port.rs','function':'port',
            'proof_source':'equiv.lean','equivalence':'Port.source_equiv'}

    def prepare(self, request=None):
        save(self.root/'request.json', request or self.request)
        return prepare(self.root/'request.json')

    def test_request_is_explicit_and_invalid_bindings_are_rejected(self):
        self.assertFalse(self.prepare()[3])
        for field, value in [('source','absent.rs'), ('proof_source','absent.lean'),
                             ('function','x; injected'), ('equivalence','foo ()')]:
            r = copy.deepcopy(self.request); r['rust_port'][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError): self.prepare(r)
        for change in [{'target':'lean'},{'language':'rust'}]:
            r = copy.deepcopy(self.request); r.update(change)
            with self.assertRaises(ValueError): self.prepare(r)
        r = copy.deepcopy(self.request);r['rust_port']['unchecked']=True
        with self.assertRaises(ValueError): self.prepare(r)

    def test_extraction_uses_frozen_port_bytes(self):
        request, _, program, _ = self.prepare()
        out=self.root/'out';out.mkdir();(out/'rust-port.rs').write_text('frozen port')
        (self.root/'port.rs').write_text('changed live source')
        work=self.root/'work';work.mkdir()
        tool=self.root/'tool';tool.write_text('tool')
        lib=self.root/'model';lib.mkdir();(lib/'Aeneas.olean').write_text('model')
        class Runner:
            def run(self, label, command, **kwargs):
                if label=='extract': (work/'input.llbc').write_text('test-only LLBC placeholder')
        with patch('numerics.rust.tools', return_value={'charon':tool,'aeneas':tool,'lean_lib':lib}):
            extract(program,b'python source',request,out,work,Runner())
        self.assertEqual((out/'rust/src/original.rs').read_text(),'frozen port')
        self.assertIn('original::port(', (out/'rust/src/lib.rs').read_text())

    def test_current_port_and_proof_freshness(self):
        source=self.root/'source.py';source.write_text('source')
        sources={name:{'path':str(self.root/name),'sha256':sha(self.root/name)}
                 for name in ['port.rs','equiv.lean']}
        save(self.root/'result.json',{'status':'certified','source_path':str(source),
             'source_sha256':sha(source),'artifacts':{},'rust_port_sources':sources})
        self.assertEqual(audit_run(self.root)['status'],'fresh')
        for name in sources:
            p=self.root/name;original=p.read_bytes();p.write_text('mutation')
            with self.assertRaisesRegex(ValueError,'Rust port or equivalence proof source changed'):
                audit_run(self.root)
            self.assertEqual(audit_run(self.root, frozen=True)['status'],'fresh')
            p.write_bytes(original)

    def test_replay_copies_frozen_port_without_rerunning_extraction(self):
        request, source, program, _ = self.prepare()
        frozen=self.root/'saved';(frozen/'lean/Workflow').mkdir(parents=True)
        request['source']='source.py';request['rust_port']['source']='rust-port.rs'
        request['rust_port']['proof_source']='lean/Workflow/RustEquiv.lean'
        (frozen/'source.py').write_bytes(source.read_bytes())
        (frozen/'rust-port.rs').write_text('saved port')
        (frozen/'lean/Workflow/RustEquiv.lean').write_text('saved proof')
        (frozen/'lean/Workflow/Kernel.lean').write_text(kernel_source(program,request['specification']))
        save(frozen/'request.json',request)
        save(frozen/'result.json',{'status':'certified','artifacts':{},'completed_stages':['lean_root_checked']})
        save(frozen/'analysis.json',{'accepted_bounds':{n:'1' for n in program.outputs}})
        def fake_check(output,*args,reuse=True):
            self.assertFalse(reuse)
            self.assertEqual((output/'rust-port.rs').read_text(),'saved port')
            self.assertEqual((output/'lean/Workflow/RustEquiv.lean').read_text(),'saved proof')
        with patch('numerics.rust.tools',return_value={'lean_lib':self.root}), \
             patch('numerics.rust.model_files',return_value={}), \
             patch('numerics.workflow.check_lean',side_effect=fake_check):
            save(frozen/'aeneas-model.json',{})
            replay_run(frozen,self.root/'replay')


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1' and
                     os.environ.get('FLARE_NUMERICS_RUST_TOOLS'),
                     'Set FLARE_NUMERICS_RUST_TOOLS to a local tool config for fresh Rust-port tests')
class ExplicitPortLeanTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='flare-port-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.source = self.root/'source.py'
        self.source.write_text('def identity(x):\n    return x\n')
        self.port = self.root/'port.rs'
        self.port.write_text('pub fn port(x: f64) -> f64 { x }\n')
        self.proof = self.root/'equiv.lean'
        self.proof.write_text('''module
public import Workflow.Kernel
public import Workflow.Generated.Funs
@[expose] public section
namespace Port
theorem source_equiv (a0 : Float) :
    Workflow.Generated.kernel a0 = .ok (Workflow.kernel a0) := by
  rfl
end Port
''')
        config = json.loads(Path(os.environ['FLARE_NUMERICS_RUST_TOOLS']).read_text())
        self.request = {'schema':'numerics-request-v1','language':'python','source':'source.py',
            'function':'identity','target':'rust-aeneas','domain':{'x':['-1','1']},
            'specification':['x'],'outputs':[{'name':'x','unit':'m','limit':'1/1000000'}],
            'rust_tools':config['rust_tools'],
            'rust_port':{'source':'port.rs','function':'port','proof_source':'equiv.lean',
                         'equivalence':'Port.source_equiv'}}

    def run_port(self):
        save(self.root/'request.json',self.request)
        return certify(self.root/'request.json',self.root/'run')

    def test_actual_port_extraction_and_saved_proof_replay(self):
        result = self.run_port()
        self.assertEqual(result['status'],'certified',result.get('error'))
        self.assertIn('rust_source_extracted',result['completed_stages'])
        self.assertEqual((self.root/'run/rust/src/original.rs').read_bytes(),self.port.read_bytes())
        with patch('numerics.rust.extract',side_effect=AssertionError('extractor called')):
            self.assertEqual(replay_run(self.root/'run',self.root/'replay')['status'],'replayed')

    def test_false_equivalence_is_rejected_by_lean(self):
        self.port.write_text('pub fn port(x: f64) -> f64 { x + x }\n')
        result = self.run_port()
        self.assertEqual(result['status'],'unresolved')
        self.assertEqual(result['failure_stage'],'lean-rust-equivalence')
        self.assertNotIn('lean_root_checked',result['completed_stages'])

    def test_equivalence_axiom_is_rejected_by_the_root_audit(self):
        text = self.proof.read_text().replace('theorem source_equiv','axiom source_equiv')
        self.proof.write_text(text.replace(' := by\n  rfl',''))
        result = self.run_port()
        self.assertEqual(result['status'],'unresolved')
        self.assertEqual(result['failure_stage'],'lean-proof')
        self.assertIn('Unexpected axiom',
                      (self.root/'run/runs/lean-proof/stdout.txt').read_text())

if __name__ == '__main__': unittest.main()
