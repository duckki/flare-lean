"""Scientific source, typed shapes, runtime identity and retained Rust API controls."""
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from numerics.frontend import Unsupported,execute,parse
from numerics.integration import Session,ToolError
from numerics.workflow import ROOT,audit_run,certify,prepare,replay_run,save,sha


EXAMPLES=ROOT/'examples/numerics/scientific'
SELECTED_TOOLS=json.loads(Path(os.environ['FLARE_NUMERICS_RUST_TOOLS']).read_text()) if os.environ.get('FLARE_NUMERICS_RUST_TOOLS') else {}


def request(root,name,**updates):
    r=json.loads((EXAMPLES/(name+'.json')).read_text());r['source']=str(EXAMPLES/r['source'])
    if 'rust_port' in r:
        r['rust_port']={**r['rust_port'],**{f:str(EXAMPLES/r['rust_port'][f]) for f in ['source','proof_source']}}
    tools=SELECTED_TOOLS
    if r['language']=='julia' and tools.get('runtimes',{}).get('julia'):r['source_runtime']=tools['runtimes']['julia']
    if r.get('target')=='rust-aeneas' and tools.get('rust_tools'):r['rust_tools']=tools['rust_tools']
    save(root/'request.json',{**r,**updates});return root/'request.json'


class ScientificAdmissionTests(unittest.TestCase):
    def test_actual_sources_keep_shapes_helpers_loops_and_all_dense_outputs(self):
        for name,outputs in [('calibration_python',2),('calibration_julia',2),('dense_update',6)]:
            _,_,program,questions=prepare(EXAMPLES/(name+'.json'))
            self.assertFalse(questions);self.assertEqual(len(program.outputs),outputs)
            self.assertEqual(program.scientific['schema'],'scientific-arrays-v1')
            if name=='dense_update':
                self.assertEqual(program.scientific['outputs'],[[2],[2,2]])
                self.assertGreater(len(program.nodes),64)
                self.assertTrue(program.scientific['loops'])

    def test_dtype_promotions_blas_broadcast_and_alias_mutation_are_closed(self):
        source=(EXAMPLES/'calibration.py').read_text();shapes={n:[2] for n in ['values','gains','offsets']}
        variants=[source.replace('scaled = np.multiply(values, gains)','values += gains\n    scaled = np.add(values, offsets)'),source.replace('np.multiply(values, gains)','np.matmul(values, gains)'),
                  source.replace('np.multiply(values, gains)','values @ gains'),
                  source.replace('np.multiply(values, gains)','np.multiply(values, gains, out=values)'),
                  source.replace('scaled = np.multiply(values, gains)','values[0] = gains[0]\n    scaled = values'),
                  source.replace('scaled = np.multiply(values, gains)','scaled = values'),
                  source.replace('np.multiply(values, gains)','np.array([values[0], values[1]], dtype=np.float32)'),
                  source.replace('np.multiply(values, gains)','values.astype(np.float64)'),
                  source.replace('np.multiply(values, gains)','np.add.reduce(values)'),
                  source.replace('np.multiply(values, gains)','values * 9007199254740993')]
        for value in variants:
            with self.subTest(value=value),self.assertRaises(Unsupported):parse('python',value,'calibrate',scientific_arrays=shapes)
        with self.assertRaisesRegex(Unsupported,'broadcasting'):parse('python',source,'calibrate',scientific_arrays={**shapes,'gains':[1,2]})
        with self.assertRaises(Unsupported):parse('python',source.replace('return np.add(scaled, offsets)','return values.T'),'calibrate',scientific_arrays={n:[2,2] for n in shapes})

    def test_transpose_view_prevents_later_source_mutation(self):
        source='import numpy as np\ndef run(values):\n    output = np.add(values, 0.0)\n    view = output.T\n    output[0,0] = 1.0\n    return np.add(output, view)\n'
        with self.assertRaisesRegex(Unsupported,'view mutation'):
            parse('python',source,'run',scientific_arrays={'values':[2,2]})

    def test_julia_uses_one_based_indices_and_preserves_argument_types(self):
        source=(EXAMPLES/'calibration.jl').read_text();shapes={n:[2] for n in ['values','gains','offsets']}
        for value in [source.replace('1:length(values)','0:length(values)'),source.replace('value * gain','muladd(value, gain, 0.0)'),
                      source.replace('output[i] =','values[i] ='),source.replace('value * gain','value .* gain'),source.replace('affine(values[i],','affine(0,')]:
            with self.assertRaises(Unsupported):parse('julia',value,'calibrate',scientific_arrays=shapes)
        with self.assertRaises(Unsupported):parse('julia',source,'calibrate',scientific_arrays={**shapes,'values':[]})

    def test_order_changes_have_observable_native_results(self):
        shapes={'values':[3]}
        source='import numpy as np\ndef run(values):\n    out = np.zeros(1, dtype=np.float64)\n    out[0] = (values[0]+values[1])+values[2]\n    return out\n'
        original=parse('python',source,'run',scientific_arrays=shapes)
        changed=parse('python',source.replace('(values[0]+values[1])+values[2]','values[0]+(values[1]+values[2])'),'run',scientific_arrays=shapes)
        self.assertEqual(execute(original,[1e16,-1e16,1.]),(1.,));self.assertEqual(execute(changed,[1e16,-1e16,1.]),(0.,))
        self.assertNotEqual(original.record(),changed.record())

    def test_julia_loop_counter_shadow_does_not_change_outer_index(self):
        source=(EXAMPLES/'calibration.jl').read_text().replace('    output = zeros','    i = 1\n    output = zeros').replace('    return output','    output[1] = output[i]\n    return output')
        program=parse('julia',source,'calibrate',scientific_arrays={n:[2] for n in ['values','gains','offsets']})
        self.assertEqual(execute(program,[1.,2.,3.,4.,0.,0.]),(3.,8.))

    def test_independent_decimal_reference_preserves_all_original_digits(self):
        from numerics.collection_spec import specification
        _,_,program,_=prepare(EXAMPLES/'calibration_python.json')
        reference={'kind':'collections','bindings':[],'outputs':['values*gains+offsets+0.50000000000000000000000001']}
        text='\n'.join(specification(reference,program))
        self.assertIn('50000000000000000000000001 : ℝ',text)
        self.assertIn('100000000000000000000000000',text)

    def test_runtime_version_mismatch_is_a_setup_error(self):
        from numerics.scientific_runtime import admit
        _,_,program,_=prepare(EXAMPLES/'calibration_julia.json')
        with self.assertRaises(ToolError) as caught:admit(program,{'version':'julia version 1.11.70'})
        self.assertEqual(caught.exception.kind,'unsupported_tool_version')

    def test_ordinary_frontends_keep_their_identity_and_need_no_numpy(self):
        with patch('numerics.scientific_runtime.numpy',side_effect=AssertionError('NumPy called')):
            program=parse('python','def identity(x):\n    return x\n','identity')
            self.assertNotIn('scientific',program.record())
            prepare(EXAMPLES/'calibration_python.json')


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1','Run make numerics-check')
class ScientificLeanTests(unittest.TestCase):
    def setUp(self):
        self.parent=ROOT/'.cache/numerics-generated';self.parent.mkdir(parents=True,exist_ok=True)

    def test_numpy_calibration_and_dense_source_certify_and_cold_replay_without_numpy(self):
        with tempfile.TemporaryDirectory(prefix='scientific-',dir=self.parent) as directory:
            root=Path(directory)
            for name in ['calibration_python','dense_update']:
                run=root/name;result=certify(request(root,name),run)
                self.assertEqual(result['status'],'certified',result.get('error'))
                self.assertTrue(result['diagnostics']['source_IR_word_agreement'])
                runtime=json.loads((run/'source-runtime.json').read_text())
                self.assertEqual(runtime['libraries'][0]['version'],'2.4.0')
                with patch.object(Session,'execute',side_effect=AssertionError('producer called')), \
                     patch('numerics.runtimes.admit_runtime',side_effect=AssertionError('runtime called')), \
                     patch('numerics.scientific_runtime.numpy',side_effect=AssertionError('NumPy called')):
                    self.assertEqual(replay_run(run,root/(name+'-replay'))['status'],'replayed')
                check=(run/'lean/Workflow/Check.lean').read_text()
                self.assertIn('sourceExec',check);self.assertIn('.shape = [2',check)
                if name=='dense_update':self.assertIn('.shape = [2, 2]',check)

    def test_wrong_reference_weakened_shape_root_and_changed_runtime_library_fail(self):
        with tempfile.TemporaryDirectory(prefix='scientific-negative-',dir=self.parent) as directory:
            root=Path(directory)
            spec={'kind':'collections','bindings':[],'outputs':['values*gains+offsets+1']}
            bad=certify(request(root,'calibration_python',specification=spec),root/'false')
            self.assertEqual((bad['status'],bad['failure_stage']),('unresolved','lean-proof'))
            decimal=json.loads(request(root,'calibration_python').read_text())
            shifted=root/'shifted.py';shifted.write_text((EXAMPLES/'calibration.py').read_text().replace('np.add(scaled, offsets)','np.add(np.add(scaled, offsets), 0.5)'))
            decimal.update(source=str(shifted),specification={'kind':'collections','bindings':[],'outputs':['values*gains+offsets+0.50000000000000000000000001']})
            save(root/'decimal.json',decimal);bad=certify(root/'decimal.json',root/'decimal')
            self.assertEqual((bad['status'],bad['failure_stage']),('unresolved','lean-proof'))
            run=root/'valid';self.assertEqual(certify(request(root,'calibration_python'),run)['status'],'certified')
            proof=run/'lean/Workflow/Proof.lean';text=proof.read_text().replace('theorem certificate (p0','theorem unused_certificate (p0')
            text+='\nnamespace Workflow.Certificate\nabbrev certificate := scalar_certificate\nend Workflow.Certificate\n';proof.write_text(text)
            result=json.loads((run/'result.json').read_text());result['artifacts']['lean/Workflow/Proof.lean']=sha(proof);save(run/'result.json',result)
            with self.assertRaisesRegex(RuntimeError,'lean-root-check'):replay_run(run,root/'weakened')
            runtime=run/'source-runtime.json';record=json.loads(runtime.read_text())
            fake=root/'runtime.so';fake.write_text('original');record['libraries'][0]['files']={str(fake):sha(fake)}
            save(runtime,record);result['artifacts']['source-runtime.json']=sha(runtime);save(run/'result.json',result)
            fake.write_text('changed')
            with self.assertRaisesRegex(ValueError,'Source runtime library changed'):audit_run(run)

    @unittest.skipUnless(SELECTED_TOOLS.get('runtimes',{}).get('julia'),'Requires selected Julia runtime')
    def test_original_julia_vector_api_and_replay(self):
        with tempfile.TemporaryDirectory(prefix='scientific-julia-',dir=self.parent) as directory:
            root=Path(directory);run=root/'valid';result=certify(request(root,'calibration_julia'),run)
            self.assertEqual(result['status'],'certified',result.get('error'))
            with patch('numerics.runtimes.admit_runtime',side_effect=AssertionError('Julia called')):
                self.assertEqual(replay_run(run,root/'replay')['status'],'replayed')


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1' and os.environ.get('FLARE_NUMERICS_RUST_TOOLS'),'Optional Rust proof tools/Julia runtime')
class ScientificRustTests(unittest.TestCase):
    def test_retained_array_api_real_loop_and_false_port(self):
        parent=ROOT/'.cache/numerics-generated';parent.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='scientific-rust-',dir=parent) as directory:
            root=Path(directory);run=root/'valid';path=request(root,'calibration_rust',language='python',source=str(EXAMPLES/'calibration.py'),source_runtime=None);result=certify(path,run)
            self.assertEqual(result['status'],'certified',result.get('error'))
            self.assertIn('while i < values.len()', (run/'rust-port.rs').read_text())
            with patch('numerics.rust.extract',side_effect=AssertionError('extractor called')):
                self.assertEqual(replay_run(run,root/'replay')['status'],'replayed')
            r=json.loads(path.read_text());port=root/'wrong.rs';port.write_text(Path(r['rust_port']['source']).read_text().replace('value * gain + offset','value + gain + offset'))
            r['rust_port']['source']=str(port);save(root/'wrong.json',r)
            bad=certify(root/'wrong.json',root/'wrong')
            self.assertEqual((bad['status'],bad['failure_stage']),('unresolved','lean-rust-equivalence'))


if __name__=='__main__':unittest.main()
