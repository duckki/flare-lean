"""Array source admission, actual word semantics, typed roots and frozen replay."""
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from numerics.frontends.scalar import Unsupported, execute, parse, word
from numerics.integrations.registry import Session
from numerics.frontends.python_arrays import load_arrays
from numerics.workflow.certification import ROOT, certify, prepare, replay_run, save, sha


EXAMPLES=ROOT/'examples/numerics/arrays'


class ArrayAdmissionTests(unittest.TestCase):
    def test_matrix_vector_and_matrix_matrix_match_actual_python_words(self):
        for name in ['linear_prediction','calibration_product','dot_projection','state_prediction4','one_entry']:
            request,source,program,questions=prepare(EXAMPLES/(name+'.json'))
            self.assertFalse(questions)
            original=load_arrays(source.read_text(),program.function,program.arrays)
            for values in [[float((i%5)-2)/2 for i in range(len(program.inputs))],
                           [-0.0 if i%2 else 0.0 for i in range(len(program.inputs))],
                           [float.fromhex('0x0.0000000000001p-1022')]*len(program.inputs)]:
                self.assertEqual(tuple(map(word,original(*values))),tuple(map(word,execute(program,values))))

    def test_shapes_aliasing_mutation_indices_and_order_are_rejected(self):
        r,source,_,_=prepare(EXAMPLES/'calibration_product.json')
        text=source.read_text()
        variants=[
            text.replace('[[0.0, 0.0], [0.0, 0.0]]','[[0.0, 0.0]] * 2'),
            text.replace('result = [[0.0, 0.0], [0.0, 0.0]]','result = left'),
            text.replace('result[i][j] = total','left[i][j] = total'),
            text.replace('right[k][j]','right[2][j]'),
            text.replace('right[k][j]','right[k][-1]'),
            text.replace('left[i][k] * right[k][j]','left[i][1-k] * right[1-k][j]'),
            text.replace('def compose(', 'def compose(').replace(' -> list[list[float]]', ' -> dangerous()'),
            text.replace('result = [[0.0, 0.0], [0.0, 0.0]]','result = [[0.0, 0.0], [0.0]]'),
        ]
        for variant in variants:
            with self.subTest(source=variant), self.assertRaises(Unsupported):
                parse('python',variant,'compose',python_arrays=r['python_arrays'])
        with self.assertRaisesRegex(Unsupported,'shape'):
            parse('python',text,'compose',python_arrays={'left':[2,3],'right':[2,2]})
        with self.assertRaisesRegex(Unsupported,'shape assertion'):
            parse('python',text.replace('len(left) == 2','len(left) == 3'),'compose',python_arrays=r['python_arrays'])

    def test_no_implicit_numpy_blas_or_rust_route(self):
        r,source,_,_=prepare(EXAMPLES/'linear_prediction.json')
        with self.assertRaises(Unsupported):
            parse('python','import numpy\n'+source.read_text(),'predict',python_arrays=r['python_arrays'])
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);(root/'source.py').write_text(source.read_text())
            save(root/'request.json',{**r,'source':'source.py','target':'rust-aeneas'})
            with self.assertRaisesRegex(Unsupported,'fixed-array profile'):
                prepare(root/'request.json')


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1','Run make numerics-check')
class ArrayLeanTests(unittest.TestCase):
    def test_array_applications_certify_and_replay_without_inference(self):
        with tempfile.TemporaryDirectory(prefix='flare-array-applications-') as directory:
            root=Path(directory)
            for name in ['linear_prediction','calibration_product','dot_projection','state_prediction4','one_entry']:
                result=certify(EXAMPLES/(name+'.json'),root/name)
                self.assertEqual(result['status'],'certified',result.get('error'))
                self.assertTrue(result['diagnostics']['source_IR_word_agreement'])
                with patch.object(Session,'execute',side_effect=AssertionError('producer called')):
                    replayed=replay_run(root/name,root/(name+'-replayed'))
                self.assertEqual(replayed['status'],'replayed')
            # A resealed weakened root must still fail the independent array type.
            run=root/'calibration_product';path=run/'lean/Workflow/Proof.lean'
            text=path.read_text();start=text.index('theorem certificate (p0')
            changed=text[start:].replace('((arrayKernel p0 p1).size = 2)','True',1)
            changed=changed.replace('  · rw [array_equiv]; rfl','  · trivial',1)
            text=text[:start]+changed
            path.write_text(text)
            recorded=json.loads((run/'result.json').read_text())
            recorded['artifacts']['lean/Workflow/Proof.lean']=sha(path);save(run/'result.json',recorded)
            with self.assertRaisesRegex(RuntimeError,'lean-root-check'):
                replay_run(run,root/'weakened-root')

    def test_false_exact_matrix_specification_fails_in_lean(self):
        with tempfile.TemporaryDirectory(prefix='flare-array-rejection-') as directory:
            root=Path(directory);r,source,_,_=prepare(EXAMPLES/'calibration_product.json')
            (root/'source.py').write_text(source.read_text())
            wrong=copy.deepcopy(r);wrong['source']='source.py';wrong['specification']['expression']='right @ left'
            save(root/'request.json',wrong)
            result=certify(root/'request.json',root/'wrong-specification')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-proof'))
            self.assertNotIn('lean_root_checked',result['completed_stages'])

    def test_checked_array_allowance_above_budget_replays_as_a_diagnostic(self):
        with tempfile.TemporaryDirectory(prefix='flare-array-budget-') as directory:
            root=Path(directory);r,source,_,_=prepare(EXAMPLES/'calibration_product.json')
            (root/'source.py').write_text(source.read_text())
            r['source']='source.py';r['outputs'][0]['limit']='1/1000000000000000000000000000000'
            save(root/'request.json',r)
            result=certify(root/'request.json',root/'above-budget')
            self.assertEqual(result['status'],'budget_not_met',result.get('error'))
            self.assertTrue(all(target['evidence']=='checked' for target in result['outputs']))
            replayed=replay_run(root/'above-budget',root/'replay')
            self.assertEqual(replayed['certificate_status'],'budget_not_met')


if __name__=='__main__': unittest.main()
