"""Power correlations, typed enclosure rules and independently rejected evidence."""
from fractions import Fraction as Q
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from numerics.analysis import enclosure
from numerics.analysis import scalar
from numerics.frontends.scalar import Unsupported, parse
from numerics.integrations.registry import ARITHMETIC, Session, validate
from numerics.workflow.certification import ROOT, certify, prepare, replay_run, save


class EnclosureInferenceTests(unittest.TestCase):
    def test_signed_and_degenerate_power_ranges(self):
        x = ('variable', 'a0')
        for endpoints, power, expected in [
                ((-2, 3), 2, (0, 9)), ((-3, -2), 2, (4, 9)),
                ((2, 3), 2, (4, 9)), ((-2, 3), 3, (-8, 27)),
                ((-2, 3), 0, (1, 1)), ((0, 0), 4, (0, 0))]:
            with self.subTest(endpoints=endpoints, power=power):
                self.assertEqual(scalar.interval(('pow', x, power), {'a0':endpoints}), expected)

    def test_square_floor_closes_native_and_exact_denominators(self):
        for offset in ['1.0', '2.0', '4.0']:
            program = parse('python', 'def f(x):\n    return 1.0/(x*x+'+offset+')\n', 'f')
            summaries, _ = scalar.analyze_box(program, {'x':['-1','1']})
            denominator = summaries[program.nodes[-1].args[1]]
            self.assertGreater(denominator.c-denominator.w-denominator.e, Q(offset)*Q(9,10))
        program = parse('python', 'def f(x):\n    return 1.0/(x*x)\n', 'f')
        with self.assertRaisesRegex(ValueError, 'positive native and exact denominator'):
            scalar.analyze_box(program, {'x':['-1','1']})

    def test_unimplemented_rules_and_rounding_modes_are_rejected(self):
        for tree in [('div', ('constant', Q(1)), ('constant', Q(2))),
                     ('pow', ('variable', 'a0'), 17)]:
            with self.assertRaisesRegex(ValueError, 'Unsupported shared enclosure rule'):
                enclosure.expression(tree)
        program = parse('python', 'def f(x):\n    return x*x\n', 'f')
        with self.assertRaisesRegex(Unsupported, 'arithmetic model'):
            validate({'arithmetic':{**ARITHMETIC,'rounding':'toward-zero'}}, program)


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION') == '1', 'Run make numerics-check')
class EnclosureLeanTests(unittest.TestCase):
    def request(self, directory, name='regularized_gain_lean.json', **updates):
        request, source, _, _ = prepare(ROOT/'examples/numerics/enclosures'/name)
        path = directory/'request.json'
        save(path, {**request,'source':str(source), **updates})
        return path

    def test_regularized_gain_family_and_inference_free_replay(self):
        with tempfile.TemporaryDirectory(prefix='enclosure-tests-',dir=ROOT/'.cache/numerics-generated') as directory:
            root = Path(directory)
            for index, endpoints in enumerate([['-1','1'],['-2','2'],['-4/3','4/3']]):
                request = self.request(root, domain={'x':endpoints})
                run = root/str(index)
                result = certify(request, run)
                self.assertEqual(result['status'],'certified',result.get('error'))
                details = json.loads((run/'evidence.json').read_text())['records'][0]['details']
                self.assertEqual(details['rule_checker'],'Flare.Analysis.IntervalExpression.Expr.check_sound')
                with patch.object(Session,'execute',side_effect=AssertionError('producer called')), \
                     patch('numerics.analysis.enclosure.proof',side_effect=AssertionError('inference called')):
                    self.assertEqual(replay_run(run,root/(str(index)+'-replay'))['status'],'replayed')

    def test_zero_polynomial_and_negated_square_keep_the_source_schedule(self):
        with tempfile.TemporaryDirectory(prefix='enclosure-tests-',dir=ROOT/'.cache/numerics-generated') as directory:
            root=Path(directory)
            (root/'source.py').write_text('def f(x):\n    return x-x, -(x*x)\n')
            limit=str(Q(3,2**54))
            save(root/'request.json',{'schema':'numerics-request-v1','language':'python',
                'source':'source.py','function':'f','domain':{'x':['-1','1']},
                'specification':['0','-(x*x)'],
                'outputs':[{'name':name,'unit':'1','limit':limit} for name in ['zero','negative']]})
            run=root/'run'
            result=certify(root/'request.json',run)
            self.assertEqual(result['status'],'certified',result.get('error'))
            self.assertEqual(result['producer_validation'],'lean-scalar-interval-v1')
            self.assertEqual(replay_run(run,root/'replay')['status'],'replayed')

    def test_corrupt_enclosure_rule_rewrite_and_leaf_premise_fail_in_lean(self):
        with tempfile.TemporaryDirectory(prefix='enclosure-tests-',dir=ROOT/'.cache/numerics-generated') as directory:
            root = Path(directory)
            request = self.request(root)
            original = enclosure.expression
            with patch('numerics.analysis.enclosure.expression',side_effect=lambda tree:original(tree).replace('(.add','(.mul')):
                result = certify(request,root/'bad-rule')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
            # The source polynomial remains x*x. A proposed cubic interpretation
            # may have plausible endpoints, but its rewrite is still false.
            renderer = scalar.render
            with patch('numerics.analysis.scalar.render',side_effect=lambda tree:renderer(tree).replace(' ^ 2)',' ^ 3)')):
                result = certify(request,root/'bad-rewrite')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
            atom = enclosure.atom
            with patch('numerics.analysis.enclosure.atom',side_effect=lambda name,lo,hi,value:
                    atom(name, Q(1,2) if name=='a0' else lo, hi, value)):
                result = certify(request,root/'bad-premise')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
            for label in ['bad-rule','bad-rewrite','bad-premise']:
                result=json.loads((root/label/'result.json').read_text())
                self.assertNotIn('lean_root_checked',result['completed_stages'])
                self.assertNotIn('accepted_bounds',json.loads((root/label/'analysis.json').read_text()))


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION') == '1' and
                     os.environ.get('FLARE_NUMERICS_ANALYSIS_TOOLS'), 'Select real Gappa and FPTaylor tools')
class EnclosureToolTests(unittest.TestCase):
    def test_two_tools_use_shared_power_rules_and_replay_without_producers(self):
        configuration=json.loads(Path(os.environ['FLARE_NUMERICS_ANALYSIS_TOOLS']).read_text())
        tools=configuration.get('analysis_tools',configuration)
        with tempfile.TemporaryDirectory(prefix='enclosure-tools-',dir=ROOT/'.cache/numerics-generated') as directory:
            root=Path(directory)
            for producer in ['gappa','fptaylor']:
                for function in ['square','quartic']:
                    name=function+'_'+producer
                    request,source,_,_=prepare(ROOT/'examples/numerics/enclosures'/(name+'.json'))
                    save(root/'request.json',{**request,'source':str(source),'analysis_tools':tools})
                    run=root/name
                    result=certify(root/'request.json',run)
                    self.assertEqual(result['status'],'certified',result.get('error'))
                    details=json.loads((run/'evidence.json').read_text())['records'][0]['details']
                    self.assertEqual(details['rule_checker'],'Flare.Analysis.IntervalExpression.Expr.check_sound')
                    candidates=details['queried_error_radii' if producer=='gappa' else 'raw_candidate_bounds']
                    self.assertEqual([item['bound'] for item in result['outputs']],candidates)
                    with patch.object(Session,'tool',side_effect=AssertionError('tool admission called')), \
                         patch.object(Session,'execute',side_effect=AssertionError('producer called')), \
                         patch('numerics.analysis.enclosure.proof',side_effect=AssertionError('inference called')):
                        self.assertEqual(replay_run(run,root/(name+'-replay'))['status'],'replayed')


if __name__ == '__main__':
    unittest.main()
