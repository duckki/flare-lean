"""Typed operation evidence must survive Lean checking and reject false annotations."""
from dataclasses import replace
from fractions import Fraction as Q
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from numerics.analysis import checked_bounds
from numerics.frontends.scalar import parse
from numerics.integrations.registry import Session
from numerics.paths import ROOT
from numerics.workflow.certification import Runner, certify, prepare, replay_run, save


class CheckedBoundsTests(unittest.TestCase):
    def test_products_keep_compact_annotations_and_exact_zero(self):
        for name in ['power32', 'power256', 'zero_product', 'zero_energy']:
            request, _, program, _ = prepare(ROOT/'examples/numerics/typed-evidence'/(name+'.json'))
            bounds, steps = checked_bounds.infer(program, request['domain'])
            self.assertEqual(len(steps), len(program.nodes))
            self.assertTrue(all(len(str(step)) < 3000 for step in steps))
            end = bounds[program.outputs[0]]
            self.assertLessEqual(end.e, Q(request['outputs'][0]['limit']))
            if name.startswith('zero'):
                self.assertEqual(end.e, 0)
                self.assertEqual(steps[-1]['rule'], 'mul_zero')

    def test_tiny_constant_chains_do_not_grow_rational_evidence_exponentially(self):
        source='def f(x):\n    y=1e-300\n'+'    y=y*y\n'*31+'    return y\n'
        program=parse('python',source,'f')
        self.assertTrue(checked_bounds.supported(program))
        bounds,steps=checked_bounds.infer(program,{'x':['-1','1']})
        self.assertEqual(len(steps),32)
        for bound in bounds.values():
            self.assertTrue(all(max(q.numerator.bit_length(),q.denominator.bit_length()) <=
                                checked_bounds.MAX_RATIONAL_BITS for q in [bound.c,bound.w,bound.i,bound.e]))
        self.assertTrue(all(step['rule']=='mul' for step in steps[1:]))
        with self.assertRaisesRegex(ValueError,'rational work limit'):
            checked_bounds.infer(program,{'x':[str(2**5000),str(2**5000)]})

    def test_profile_excludes_other_arithmetic_and_unchecked_overflow(self):
        for source in ['def f(x):\n    return x+1.0\n', 'def f(x):\n    return 1.0/x\n']:
            self.assertFalse(checked_bounds.supported(parse('python', source, 'f')))
        program = parse('python','def f(x):\n    return x*x\n','f')
        with self.assertRaisesRegex(ValueError, 'finite nearest-rounding profile'):
            checked_bounds.infer(program, {'x':[str(2**600), str(2**600)]})


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION') == '1', 'Run make numerics-check')
class CheckedBoundsLeanTests(unittest.TestCase):
    def request(self, root, name):
        request, source, _, _ = prepare(ROOT/'examples/numerics/typed-evidence'/(name+'.json'))
        path = root/'request.json';save(path,{**request,'source':str(source)})
        return path

    def test_products_and_exact_zero_finish_the_root_and_replay(self):
        with tempfile.TemporaryDirectory(prefix='typed-products-',dir=ROOT/'.cache/numerics-generated') as tmp:
            root=Path(tmp)
            for name in ['power32','power256','zero_product','zero_energy','tiny_constants']:
                request=self.request(root,name)
                result=certify(request,root/name)
                self.assertEqual(result['status'],'certified',result.get('error'))
                self.assertEqual(result['producer_validation'],'lean-typed-product-v1')
                if name.startswith('zero'):
                    self.assertEqual(result['outputs'][0]['bound'],'0')
                with patch.object(Session,'execute',side_effect=AssertionError('producer called')), \
                     patch.object(checked_bounds,'infer',side_effect=AssertionError('inference called')):
                    self.assertEqual(replay_run(root/name,root/(name+'-replay'))['status'],'replayed')

    def test_incoming_error_and_underflow_controls_are_kernel_checked(self):
        with tempfile.TemporaryDirectory(prefix='typed-controls-',dir=ROOT/'.cache/numerics-generated') as tmp:
            root=Path(tmp)
            source=root/'Controls.lean'
            source.write_bytes((ROOT/'benchmarks/numerics/integrations/CheckedControls.lean.txt').read_bytes())
            Runner(root).run('controls',['lake','env','lean',source])

    def test_false_range_error_rounding_and_exactness_are_rejected(self):
        original=checked_bounds.infer
        def corrupt(kind):
            def infer(program,domain):
                bounds,steps=original(program,domain)
                key=program.outputs[0]
                if kind=='exactness':steps[-1]['rule']='mul_zero'
                elif kind=='rounding':steps[-1]['rounding_allowance']='0'
                else:
                    bounds[key]=replace(bounds[key], **{'w' if kind=='range' else 'e':Q(0)})
                    steps[-1]['summary']=bounds[key].record()
                return bounds,steps
            return infer
        with tempfile.TemporaryDirectory(prefix='typed-reject-',dir=ROOT/'.cache/numerics-generated') as tmp:
            root=Path(tmp);request=self.request(root,'power32')
            for kind in ['range','error','rounding','exactness']:
                with patch.object(checked_bounds,'infer',side_effect=corrupt(kind)):
                    result=certify(request,root/kind)
                self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
                self.assertNotIn('lean_root_checked',result['completed_stages'])
                self.assertNotIn('accepted_bounds',json.loads((root/kind/'analysis.json').read_text()))


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1' and
                     os.environ.get('FLARE_NUMERICS_ANALYSIS_TOOLS'), 'Select real Gappa')
class CheckedBoundsToolTests(unittest.TestCase):
    def test_gappa_candidate_uses_the_same_typed_backend(self):
        configuration=json.loads(Path(os.environ['FLARE_NUMERICS_ANALYSIS_TOOLS']).read_text())
        with tempfile.TemporaryDirectory(prefix='typed-gappa-',dir=ROOT/'.cache/numerics-generated') as tmp:
            root=Path(tmp)
            request,source,_,_=prepare(ROOT/'examples/numerics/typed-evidence/power32_gappa.json')
            save(root/'request.json',{**request,'source':str(source),
                'analysis_tools':configuration.get('analysis_tools',configuration)})
            result=certify(root/'request.json',root/'run')
            self.assertEqual(result['status'],'certified',result.get('error'))
            details=json.loads((root/'run/evidence.json').read_text())['records'][0]['details']
            self.assertEqual(details['rule_checker'],checked_bounds.CHECKER)
            self.assertEqual(json.loads((root/'run/evidence.json').read_text())['records'][0]['constraints']['fallback_rule_checker'],checked_bounds.CHECKER)
            self.assertEqual([o['bound'] for o in result['outputs']],details['queried_error_radii'])
            with patch.object(Session,'execute',side_effect=AssertionError('producer called')), \
                 patch.object(Session,'tool',side_effect=AssertionError('tool called')):
                self.assertEqual(replay_run(root/'run',root/'replay')['status'],'replayed')


if __name__ == '__main__':
    unittest.main()
