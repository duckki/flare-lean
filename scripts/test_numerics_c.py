"""C source, object regions, counter VCs and the actual reusable Rust delivery."""
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from numerics.c_emit import memory_profile,verification_conditions
from numerics.frontend import Unsupported,execute,parse,word
from numerics.integration import Session
from numerics.workflow import ROOT,audit_run,certify,prepare,replay_run,save,sha


EXAMPLES=ROOT/'examples/numerics/c'


class CAdmissionTests(unittest.TestCase):
    def test_helpers_struct_fields_and_mutable_source_order_are_retained(self):
        for name,count,outputs in [('mean_update',2,1),('blend',6,2),('calibrate',2,1),('dot2',5,1)]:
            request,_,program,questions=prepare(EXAMPLES/(name+'.json'))
            self.assertFalse(questions)
            self.assertEqual((len(program.nodes),len(program.outputs)),(count,outputs))
            self.assertEqual(memory_profile(program),name in ('blend','dot2'))
        request,_,program,_=prepare(EXAMPLES/'blend.json')
        self.assertEqual(execute(program,[1.,-1.,.25,-.25,.5]),(.625,-.625))
        vcs=verification_conditions(program)
        self.assertEqual(vcs['loops'][0]['iterations'],2)
        self.assertEqual([a['index'] for a in vcs['accesses'] if a['operation']=='store'],[0,1])
        self.assertTrue(all(a['line']>0 for a in vcs['accesses']))
        self.assertEqual(program.inputs,('state_0','state_1','observation_0','observation_1','gain'))

    def test_double_context_converts_before_helper_arithmetic_and_preserves_signed_zero(self):
        source='double negate(double x) { return -x; } double run(double x) { return negate(0)*x; }'
        program=parse('c',source,'run')
        self.assertEqual(word(execute(program,[2.])[0]),word(-0.))
        source='double run(double x) { double y=1; y=2; return x+y; }'
        self.assertEqual(execute(parse('c',source,'run'),[3.]),(5.,))
        # C negates unsigned literals modulo 2^32; do not model them as signed integers.
        for literal in ['-1U','-0xffffffff','2147483648','1/2']:
            with self.subTest(literal=literal),self.assertRaises(Unsupported):
                parse('c','double run(double x) { return x*('+literal+'); }','run')

    def test_casts_alias_escape_mutation_and_wrong_loop_bounds_are_rejected(self):
        source=(EXAMPLES/'updates.c').read_text()
        changes=[('i < 2','i <= 2'),('i < 2','i < 3'),('unsigned int i','int i'),
            ('state[restrict static 2]','state[static 2]'),
            ('state[i] = state[i]','observation[i] = state[i]'),
            ('gain * (observation[i] - state[i])','(float)gain * (observation[i] - state[i])'),
            ('state[i] = state[i]','double *alias = state;\n        state[i] = state[i]'),
            ('state[i] = state[i]','state[i+4294967295U] = state[i]')]
        for old,new in changes:
            with self.subTest(old=old),self.assertRaises(Unsupported):parse('c',source.replace(old,new),'blend')
        for bad in ['#include <math.h>\n'+source,'double global;\n'+source,
                    source.replace('return gain * residual;','return state[0];')]:
            with self.assertRaises(Unsupported):parse('c',bad,'mean_update')

    def test_c_octal_loop_bounds_are_not_read_as_decimal(self):
        source='double run(double x) { for (unsigned int i=0; i<010; ++i) { x=x/2.0; } return x; }'
        program=parse('c',source,'run')
        self.assertEqual(program.c['loops'][0]['iterations'],8)
        self.assertEqual(execute(program,[256.]),(1.,))
        with self.assertRaises(Unsupported):parse('c','// hidden '+chr(92)+'\n'+source,'run')

    def test_reassociation_changes_native_execution_and_is_not_normalized_away(self):
        left=parse('c','double run(double x,double y,double z){return (x+y)+z;}','run')
        right=parse('c','double run(double x,double y,double z){return x+(y+z);}','run')
        self.assertNotEqual(left.record(),right.record())
        self.assertEqual(execute(left,[1e16,-1e16,1.]),(1.,))
        self.assertEqual(execute(right,[1e16,-1e16,1.]),(0.,))

    def test_legacy_profiles_do_not_gain_c_metadata_or_require_the_parser(self):
        program=parse('python','def identity(x):\n    return x\n','identity')
        self.assertNotIn('c',program.record())
        with patch('numerics.c_frontend.parser_package',side_effect=RuntimeError('parser unavailable')):
            self.assertEqual(execute(parse('rust','pub fn f(x: f64) -> f64 { x }','f'),[1.]),(1.,))
            with self.assertRaisesRegex(RuntimeError,'parser unavailable'):
                parse('c','double f(double x){return x;}','f')


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1','Run make numerics-check')
class CLeanTests(unittest.TestCase):
    def setUp(self):
        self.parent=ROOT/'.cache/numerics-generated';self.parent.mkdir(parents=True,exist_ok=True)

    def request(self,root,name='blend',**updates):
        r=json.loads((EXAMPLES/(name+'.json')).read_text())
        source=root/'source.c';source.write_bytes((EXAMPLES/r['source']).read_bytes());r['source']=str(source)
        save(root/'request.json',{**r,**updates});return root/'request.json'

    def test_original_scalar_buffer_and_struct_apis_certify_and_replay_without_compilers(self):
        with tempfile.TemporaryDirectory(prefix='c-apis-',dir=self.parent) as directory:
            root=Path(directory)
            for name in ['mean_update','blend','calibrate','dot2']:
                run=root/name;result=certify(self.request(root,name),run)
                self.assertEqual(result['status'],'certified',result.get('error'))
                record=json.loads((run/'c-runtime.json').read_text())
                self.assertEqual([m['mode'] for m in record['modes']],['debug','optimized','sanitized'])
                with patch.object(Session,'execute',side_effect=AssertionError('producer called')), \
                     patch('numerics.runtimes.admit_runtime',side_effect=AssertionError('compiler called')):
                    self.assertEqual(replay_run(run,root/(name+'-replay'))['status'],'replayed')
                if name=='blend':
                    text=(run/'lean/Workflow/Check.lean').read_text()
                    self.assertIn('Flare.Binary64.Memory.separated',text)
                    self.assertIn('sourceExec heap',text)
                    self.assertIn('final[index]! = heap[index]!',text)

    def test_false_reference_resealed_vcs_and_weakened_root_fail_the_intended_checks(self):
        with tempfile.TemporaryDirectory(prefix='c-negative-',dir=self.parent) as directory:
            root=Path(directory)
            bad=certify(self.request(root,specification=['state_0+gain*(observation_0-state_0)/2','state_1+gain*(observation_1-state_1)']),root/'wrong-reference')
            self.assertEqual((bad['status'],bad['failure_stage']),('unresolved','lean-proof'))
            run=root/'valid';self.assertEqual(certify(self.request(root),run)['status'],'certified')
            source=root/'source.c';original_source=source.read_text()
            source.write_text(original_source.replace('state[i] + gain * (observation[i] - state[i])',
                '(1.0-gain)*state[i] + gain*observation[i]'))
            with self.assertRaisesRegex(ValueError,'Original source changed'):
                audit_run(run)
            source.write_text(original_source)
            original=(run/'c-vcs.json').read_bytes()
            vcs=json.loads(original);vcs['accesses'][0]['index']=100;save(run/'c-vcs.json',vcs)
            r=json.loads((run/'result.json').read_text());r['artifacts']['c-vcs.json']=sha(run/'c-vcs.json');save(run/'result.json',r)
            with self.assertRaisesRegex(ValueError,'C verification conditions do not match'):
                replay_run(run,root/'wrong-vcs')
            (run/'c-vcs.json').write_bytes(original)
            proof=run/'lean/Workflow/Proof.lean'
            text=proof.read_text().replace('theorem certificate (heap','theorem unused_certificate (heap')
            text+='\nnamespace Workflow.Certificate\nabbrev certificate := scalar_certificate\nend Workflow.Certificate\n'
            proof.write_text(text);r['artifacts']['c-vcs.json']=sha(run/'c-vcs.json')
            r['artifacts']['lean/Workflow/Proof.lean']=sha(proof);save(run/'result.json',r)
            with self.assertRaisesRegex(RuntimeError,'lean-root-check'):
                replay_run(run,root/'weakened-root')

    def test_aliasing_premise_is_not_a_vacuous_guard(self):
        with tempfile.TemporaryDirectory(prefix='c-alias-',dir=self.parent) as directory:
            root=Path(directory)
            # A concrete overlap cannot satisfy the required region separation.
            source=root/'Alias.lean'
            source.write_text('module\nimport Flare.Binary64.Memory\nexample : Flare.Binary64.Memory.separated 1 2 0 2 := by\n  change (1+2 ≤ 0 ∨ 0+2 ≤ 1)\n  decide +kernel\n')
            from numerics.workflow import Runner
            runner=Runner(root,30)
            with self.assertRaisesRegex(RuntimeError,'alias-rejection'):
                runner.run('alias-rejection',['lake','env','lean',source],phase='check')
            self.assertIn('false', (root/'runs/alias-rejection/stdout.txt').read_text().lower())


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1' and os.environ.get('FLARE_NUMERICS_RUST_TOOLS'),
                     'Requires optional Rust proof tools')
class CRustTests(unittest.TestCase):
    def setUp(self):
        self.parent=ROOT/'.cache/numerics-generated';self.parent.mkdir(parents=True,exist_ok=True)

    def test_actual_c_api_port_and_false_bridge(self):
        with tempfile.TemporaryDirectory(prefix='c-rust-',dir=self.parent) as directory:
            root=Path(directory)
            r=json.loads((EXAMPLES/'mean_update_rust.json').read_text());r['source']=str(EXAMPLES/r['source'])
            r['rust_port']={**r['rust_port'],**{k:str(EXAMPLES/r['rust_port'][k]) for k in ['source','proof_source']}}
            r['rust_tools']=json.loads(Path(os.environ['FLARE_NUMERICS_RUST_TOOLS']).read_text())['rust_tools']
            save(root/'request.json',r);run=root/'valid';result=certify(root/'request.json',run)
            self.assertEqual(result['status'],'certified',result.get('error'))
            with patch('numerics.rust.extract',side_effect=AssertionError('extractor called')):
                self.assertEqual(replay_run(run,root/'replay')['status'],'replayed')
            port=root/'wrong.rs';port.write_text(Path(r['rust_port']['source']).read_text().replace('gain * residual','gain + residual'))
            r['rust_port']['source']=str(port);save(root/'bad.json',r)
            bad=certify(root/'bad.json',root/'wrong-port')
            self.assertEqual((bad['status'],bad['failure_stage']),('unresolved','lean-rust-equivalence'))


if __name__=='__main__':unittest.main()
