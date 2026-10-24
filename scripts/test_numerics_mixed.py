"""Mixed storage admission, model-specific evidence and Lean rejection controls."""
from dataclasses import replace
from fractions import Fraction as Q
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from numerics import scalar
from numerics.frontend import Unsupported,execute,parse,word
from numerics.integration import ARITHMETIC,Session,ToolError,arithmetic,validate
from numerics.workflow import ROOT,audit_run,certify,prepare,replay_run,save,sha

SOURCE='import numpy as np\ndef f(x):\n    return float(np.float32(x))\n'
EXAMPLES=ROOT/'examples/numerics/mixed'


class MixedStorageTests(unittest.TestCase):
    def test_profile_preserves_original_cast_sites_and_old_identities(self):
        p=parse('python',SOURCE,'f',python_mixed=True)
        self.assertEqual([(n.op,n.args) for n in p.nodes],[('round32',('a0',))])
        self.assertEqual(p.record()['schema'],'ordered-binary32-storage-binary64-v1')
        self.assertEqual(p.precision['conversion'],'narrow-nearest-even-exact-widen')
        ordinary=parse('python','def f(x):\n    return x + 1.0\n','f')
        self.assertNotIn('precision',ordinary.record())
        self.assertEqual(ordinary.record()['schema'],'ordered-binary64-v1')
        fma=parse('python','import math\ndef f(x):\n    return math.fma(x,x,1.0)\n','f',python_math=True)
        self.assertNotIn('precision',fma.record())
        self.assertEqual(fma.record()['schema'],'ordered-binary64-explicit-fma-v1')
        with self.assertRaises(Unsupported):parse('python',SOURCE,'f')

    def test_reject_aliases_shadowing_implicit_promotions_and_unpaired_casts(self):
        for source in [SOURCE.replace('numpy as np','numpy'),SOURCE.replace('numpy as np','numpy as n'),
                SOURCE.replace('float(np.float32(x))','np.float32(x)'),
                SOURCE.replace('float(np.float32(x))','float(x)'),
                SOURCE.replace('np.float32(x)','np.float64(x)'),
                SOURCE.replace('np.float32(x)','np.float32(x=x)'),
                SOURCE.replace('np.float32(x)','np.float32(x, x)'),
                SOURCE.replace('return float','float = x\n    return float'),
                SOURCE.replace('f(x)','f(np)'),
                SOURCE.replace('return float(np.float32(x))','v = np.float32(x)\n    return float(v + v)')]:
            with self.subTest(source=source),self.assertRaises(Unsupported):
                parse('python',source,'f',python_mixed=True)
        for settings in [{'python_math':True},{'scientific_arrays':{'x':[2]}},{'python_branches':True}]:
            with self.subTest(settings=settings),self.assertRaises(Unsupported):
                parse('python',SOURCE,'f',python_mixed=True,**settings)

    def test_wrong_models_and_unbridged_tools_are_not_silently_admitted(self):
        p=parse('python',SOURCE,'f',python_mixed=True);model=arithmetic(p)
        for wrong in [ARITHMETIC,{**model,'storage':'binary16'},
                {**model,'conversion':'toward-zero'},{**model,'rounding':'toward-zero'},
                {**model,'fma':'explicit'},{**model,'subnormals':'flush-to-zero'}]:
            with self.subTest(model=wrong),self.assertRaises(Unsupported):validate({'arithmetic':wrong},p)
        request,source,_,_=prepare(EXAMPLES/'stored.json')
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'request.json'
            for update in [{'producer':x} for x in ['gappa','fptaylor','precisa']]+[{'target':'rust-aeneas'}]:
                save(path,{**request,'source':str(source),**update})
                with self.subTest(update=update),self.assertRaisesRegex(Unsupported,'Mixed storage'):
                    prepare(path)

    def test_storage_allowances_use_a_safe_exponent_and_keep_incoming_error(self):
        for name in ['stored','calibrate','normalized_residual','storage_chain']:
            request,_,program,_=prepare(EXAMPLES/(name+'.json'))
            summaries,steps=scalar.analyze_box(program,request['domain'])
            for step in steps:
                if step['node'].op!='round32':continue
                parent=summaries[step['node'].args[0]];exponent=step['storage_exponent']
                self.assertGreaterEqual(Q(2)**exponent,parent.cap)
                self.assertEqual(step['bound'].e,parent.e+Q(2)**(exponent-23))
            if name=='storage_chain':self.assertGreater(summaries[program.outputs[-1]].e,summaries[program.outputs[0]].e)
        p=parse('python',SOURCE,'f',python_mixed=True)
        with self.assertRaisesRegex(ValueError,'finite binary32'):
            scalar.analyze_box(p,{'x':['0',str(Q(2)**127)]})
        for value in [-0.0,1.0+2.0**-24,1.0+3*2.0**-24,2.0**-149,2.0**-150]:
            import struct
            self.assertEqual(word(execute(p,[value])[0]),word(struct.unpack('>f',struct.pack('>f',value))[0]))


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1'
                     and sys.implementation.name=='cpython' and sys.version_info[:2] in ((3,13),(3,14)),
                     'Run make numerics-check with CPython 3.13/3.14')
class MixedStorageLeanTests(unittest.TestCase):
    def root(self):
        return tempfile.TemporaryDirectory(prefix='mixed-',dir=ROOT/'.cache/numerics-generated')

    def test_applications_and_replay_without_numpy_runtime_or_inference(self):
        with self.root() as directory:
            root=Path(directory)
            for name in ['stored','calibrate','normalized_residual','storage_chain','calibrate_tight']:
                with self.subTest(application=name):
                    run=root/name;result=certify(EXAMPLES/(name+'.json'),run)
                    expected='budget_not_met' if name=='calibrate_tight' else 'certified'
                    self.assertEqual(result['status'],expected,result.get('error'))
                    self.assertTrue(all(o['evidence']=='checked' for o in result['outputs']))
                    with patch.object(Session,'execute',side_effect=AssertionError('producer called')), \
                         patch('numerics.scalar.analyze_box',side_effect=AssertionError('inference called')), \
                         patch('numerics.mixed_runtime.numpy',side_effect=AssertionError('NumPy loaded')):
                        replay=replay_run(run,root/(name+'-replay'))
                        self.assertEqual(replay['status'],'replayed')
                        self.assertEqual(replay['certificate_status'],expected)

    def test_bad_storage_allowance_wrong_primitive_and_reference_fail_in_lean(self):
        original=scalar.analyze_box
        def lost_error(*args,**options):
            summaries,steps=original(*args,**options)
            for step in steps:
                if step['node'].op=='round32':
                    step['rho']=Q(0)
            return summaries,steps
        def lost_incoming(*args,**options):
            summaries,steps=original(*args,**options)
            for step in steps:
                if step['node'].op=='round32':step['bound']=replace(step['bound'],e=step['rho'])
            return summaries,steps
        original_expression=scalar.expression
        def wrong_primitive(node,ideal=False,**options):
            if node.op=='round32' and not ideal:return node.args[0]
            return original_expression(node,ideal=ideal,**options)
        with self.root() as directory:
            root=Path(directory)
            for label,context in [('allowance',patch('numerics.scalar.analyze_box',side_effect=lost_error)),
                                  ('incoming',patch('numerics.scalar.analyze_box',side_effect=lost_incoming)),
                                  ('primitive',patch('numerics.scalar.expression',side_effect=wrong_primitive))]:
                with context:result=certify(EXAMPLES/'calibrate.json',root/label)
                self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
                self.assertNotIn('lean_root_checked',result['completed_stages'])
            request,source,_,_=prepare(EXAMPLES/'calibrate.json')
            save(root/'request.json',{**request,'source':str(source),'specification':['gain*sample+offset+1']})
            result=certify(root/'request.json',root/'reference')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-proof'))

    def test_zero_subnormal_domains_and_runtime_identity(self):
        with self.root() as directory:
            root=Path(directory);request,source,_,_=prepare(EXAMPLES/'stored.json')
            for index,bounds in enumerate([['0','0'],[str(Q(2)**-149),str(Q(2)**-149)],['-1/3','2/3']]):
                save(root/'request.json',{**request,'source':str(source),'domain':{'x':bounds}})
                run=root/str(index);result=certify(root/'request.json',run)
                self.assertEqual(result['status'],'certified',result.get('error'))
                self.assertEqual(replay_run(run,root/(str(index)+'-replay'))['status'],'replayed')
            runtime=json.loads((run/'source-runtime.json').read_text());library=set(runtime['libraries'][0]['files'])
            with patch('numerics.runtimes.math_platform',return_value={'system':'changed'}):
                with self.assertRaisesRegex(ValueError,'platform changed'):audit_run(run)
            real_sha=sha
            with patch('numerics.workflow.sha',side_effect=lambda p:'changed' if str(p) in library else real_sha(p)):
                with self.assertRaisesRegex(ValueError,'runtime library changed'):audit_run(run)

    def test_missing_changed_or_incorrect_runtime_is_separate_from_proof_rejection(self):
        from numerics.mixed_runtime import admit
        from numerics.scientific_runtime import numpy
        _,_,program,_=prepare(EXAMPLES/'stored.json')
        np=numpy()
        with patch('numerics.scientific_runtime.numpy',side_effect=ToolError('missing_tool','no selected numpy')):
            with self.assertRaisesRegex(ToolError,'no selected numpy'):admit(program,{})
        with patch.object(np,'__version__','2.4.1'):
            with self.assertRaisesRegex(ToolError,'requires 2.4.0'):admit(program,{})
        with patch.object(np,'float32',lambda x:np.float64(x)):
            with self.assertRaisesRegex(ToolError,'preflight failed'):admit(program,{})
