"""Scalar inference acceptance, reusable families and proof-boundary controls."""
from fractions import Fraction as Q
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from numerics.analysis import scalar
from numerics.frontends.scalar import parse
from numerics.integrations.registry import Session
from numerics.workflow.certification import ROOT, certify, prepare, replay_run, save


class ScalarProposalTests(unittest.TestCase):
    def test_addition_and_small_positive_floors_avoid_fixed_grid_losses(self):
        program = parse('python', 'def f(x, y):\n    return x+y\n', 'f')
        bounds, _ = scalar.analyze_box(program, {name: ['-1','1'] for name in program.inputs})
        self.assertLess(bounds[program.outputs[0]].e, Q(2)**-50)
        request, _, program, _ = prepare(ROOT/'examples/numerics/scalar/tiny_gain.json')
        bounds, steps = scalar.analyze_box(program, request['domain'])
        denominator = program.nodes[-1].args[1]
        self.assertGreater(bounds[denominator].c-bounds[denominator].w-bounds[denominator].e, 0)
        self.assertLess(bounds[program.outputs[0]].e, Q(1,10**12))

    def test_split_search_closes_the_unchanged_tight_obligation(self):
        request, _, program, _ = prepare(ROOT/'examples/numerics/scalar/mean_update_tight.json')
        root, leaves = scalar.plan(program, request['domain'], [Q(2)**-51])
        self.assertEqual(root['domain'], request['domain'])
        self.assertEqual(len(leaves), 3)
        self.assertTrue(all(box['summaries'][program.outputs[0]].e <= Q(2)**-51 for box in leaves))

    def test_zero_candidates_are_proof_obligations_and_work_is_bounded(self):
        program = parse('python', 'def f(x, y):\n    return x+y\n', 'f')
        request = {'domain': {name: ['-1','1'] for name in program.inputs},
                   'outputs': [{'limit': '1'}]}
        candidate = scalar.proposal(program, request, ['0'])
        self.assertEqual(candidate.claims[program.outputs[0]].e, 0)
        self.assertLessEqual(candidate.details['boxes'], scalar.MAX_BOXES)
        with self.assertRaisesRegex(ValueError, 'nonnegative'):
            scalar.proposal(program, request, ['-1'])
        with self.assertRaisesRegex(ValueError, 'work limit'):
            scalar.multiply({((str(i),1),):Q(1) for i in range(17)},
                            {((str(i+17),1),):Q(1) for i in range(17)})
        with self.assertRaisesRegex(ValueError, 'work limit'):
            scalar.multiply({(('x',16),):Q(1)}, scalar.variable('x'))


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION') == '1', 'Run make numerics-check')
class ScalarLeanTests(unittest.TestCase):
    def request(self, root, example, **updates):
        request, source, _, _ = prepare(ROOT/'examples/numerics/scalar'/example)
        request = {**request, 'source': str(source), **updates}
        path = root/'request.json'; save(path, request)
        return path

    def test_tight_mean_family_and_producer_free_replay(self):
        with tempfile.TemporaryDirectory(prefix='flare-scalar-') as directory:
            root = Path(directory)
            for index, (domain, limit) in enumerate([
                (None, Q(2)**-51),
                ({'x':['-2','2'], 'z':['-1','1'], 'k':['0','1']}, Q(1,10**15)),
                ({'x':['-1/2','1/2'], 'z':['-1/4','1/4'], 'k':['0','1']}, Q(2)**-52),
            ]):
                updates = {'outputs':[{'name':'mean','unit':'m','limit':str(limit)}]}
                if domain is not None:
                    updates['domain'] = domain
                path = self.request(root, 'mean_update_tight.json', **updates)
                run = root/str(index)
                result = certify(path, run)
                self.assertEqual(result['status'], 'certified', result.get('error'))
                self.assertLessEqual(Q(result['outputs'][0]['bound']), limit)
                self.assertEqual(result['producer_validation'], 'lean-scalar-interval-v1')
                with patch.object(Session, 'execute', side_effect=AssertionError('producer called')), \
                     patch('numerics.analysis.scalar.proposal', side_effect=AssertionError('inference called')):
                    self.assertEqual(replay_run(run, root/(str(index)+'-replay'))['status'], 'replayed')

    def test_small_divisors_and_related_input_scales(self):
        with tempfile.TemporaryDirectory(prefix='flare-small-divisor-') as directory:
            root = Path(directory)
            for index, exponent in enumerate([-54,-80]):
                domain = {name:[str(Q(2)**exponent), str(Q(2)**(exponent+1))] for name in ['p','r']}
                path = self.request(root, 'tiny_gain.json', domain=domain)
                result = certify(path, root/str(index))
                self.assertEqual(result['status'], 'certified', result.get('error'))

    def test_corrupted_bounds_and_rewrite_proposals_are_rejected(self):
        with tempfile.TemporaryDirectory(prefix='flare-scalar-rejection-') as directory:
            root = Path(directory)
            (root/'source.py').write_text('def f(x,y):\n    return x+y\n')
            request = {'schema':'numerics-request-v1','language':'python','source':'source.py','function':'f',
                       'domain':{'x':['-1','1'],'y':['-1','1']}, 'specification':['x+y'],
                       'outputs':[{'name':'sum','unit':'m','limit':str(Q(2)**-50)}]}
            save(root/'request.json', request)
            original = scalar.proposal
            with patch('numerics.analysis.scalar.proposal', side_effect=lambda p,r: original(p,r,['0'])):
                result = certify(root/'request.json', root/'false-bound')
            self.assertEqual((result['status'], result['failure_stage']), ('unresolved','lean-authored'))
            self.assertNotIn('lean_root_checked', result['completed_stages'])
            renderer = scalar.render
            with patch('numerics.analysis.scalar.render', side_effect=lambda expr: renderer(expr).replace('(value a0)', '(value a1)')):
                result = certify(root/'request.json', root/'false-rewrite')
            self.assertEqual((result['status'], result['failure_stage']), ('unresolved','lean-authored'))
            self.assertNotIn('accepted_bounds', json.loads((root/'false-rewrite/analysis.json').read_text()))


if __name__ == '__main__':
    unittest.main()
