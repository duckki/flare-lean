"""Branch domains, lazy native evaluation and independently checked guard coverage."""
from fractions import Fraction as Q
import json
import math
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from numerics.branch_local import domains
from numerics.frontend import FRONTENDS, Unsupported, execute, parse, word
from numerics.integration import Session
from numerics.workflow import ROOT, certify, prepare, replay_run, save, sha


EXAMPLE=ROOT/'examples/numerics/branches/guarded_reciprocal.json'


class LocalDomainTests(unittest.TestCase):
    def test_inactive_division_is_not_executed_and_guard_endpoints_match_words(self):
        request,source,p,_=prepare(EXAMPLE)
        function=FRONTENDS['python'].load_for_diagnostics(source.read_text(),p.function)
        self.assertEqual(domains(p,request),[{'x':['1/2','2']},{'x':['0','1/2']}])
        for x in [0.0,-0.0,2**-1074,math.nextafter(.5,0.),.5,math.nextafter(.5,1.),2.]:
            self.assertEqual(word(execute(p,(x,))[0]),word(function(x)))
        # Legacy whole-domain validation still retains its original eager profile.
        legacy=parse('python',source.read_text(),p.function,python_branches=True)
        with self.assertRaises(ZeroDivisionError):execute(legacy,(0.,))

    def test_computed_guards_and_prefix_execution_need_a_broader_bridge(self):
        source=EXAMPLE.with_suffix('.py').read_text()
        for modified in [source.replace('x >= 0.5','x+1.0 >= 0.5'),
                         source.replace('    if','    x = x+1.0\n    if'),
                         source.replace('x >= 0.5','x >= x')]:
            with self.assertRaises(Unsupported):
                parse('python',modified,'guarded_reciprocal',python_branches={'domains':'guard'})
        with self.assertRaises(Unsupported):
            parse('python',source,'guarded_reciprocal',python_branches={'domains':'sampled'})


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1','Run make numerics-check')
class LocalDomainLeanTests(unittest.TestCase):
    def setUp(self):
        self.parent=ROOT/'.cache/numerics-generated';self.parent.mkdir(parents=True,exist_ok=True)

    def request(self,root,source=None,**updates):
        r,original,_,_=prepare(EXAMPLE)
        (root/'source.py').write_text(source if source is not None else original.read_text())
        save(root/'request.json',{**r,'source':'source.py',**updates})
        return root/'request.json'

    def test_local_denominator_and_strict_guard_replay_without_producer(self):
        with tempfile.TemporaryDirectory(prefix='guard-local-',dir=self.parent) as directory:
            root=Path(directory)
            for name,source,spec in [('reciprocal',None,['1/x if x>=1/2 else 0']),
                    ('strict','def guarded_reciprocal(x):\n    if x < 0.5:\n        return 0.0\n    return 1.0/x\n',
                     ['0 if x<1/2 else 1/x']),
                    ('zero','def guarded_reciprocal(x):\n    if x >= 0.0:\n        return x+1.0\n    return -x\n',
                     ['x+1 if x>=0 else -x'])]:
                request=self.request(root,source,specification=spec,domain={'x':['-1','2']})
                result=certify(request,root/name)
                self.assertEqual(result['status'],'certified',result.get('error'))
                self.assertEqual(result['producer_validation'],'lean-guard-local-v1')
                with patch.object(Session,'execute',side_effect=AssertionError('producer called')):
                    self.assertEqual(replay_run(root/name,root/(name+'-replay'))['status'],'replayed')

    def test_unreachable_bad_arm_needs_no_global_denominator_premise(self):
        with tempfile.TemporaryDirectory(prefix='guard-unreachable-',dir=self.parent) as directory:
            root=Path(directory)
            source=EXAMPLE.with_suffix('.py').read_text().replace('return 0.0','return 1.0/0.0')
            result=certify(self.request(root,source,domain={'x':['1','2']}),root/'out')
            self.assertEqual(result['status'],'certified',result.get('error'))
            self.assertEqual(replay_run(root/'out',root/'replay')['status'],'replayed')

    def test_wrong_reference_missing_guard_and_resealed_arm_are_rejected(self):
        with tempfile.TemporaryDirectory(prefix='guard-negative-',dir=self.parent) as directory:
            root=Path(directory)
            result=certify(self.request(root,specification=['1/x if x>=1/4 else 0']),root/'wrong-ref')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
            source=EXAMPLE.with_suffix('.py').read_text().replace('x >= 0.5','x < 0.5')
            result=certify(self.request(root,source),root/'wrong-guard')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','analysis'))
            run=root/'valid';self.assertEqual(certify(self.request(root),run)['status'],'certified')
            model=run/'lean/Workflow/BranchYes/Kernel.lean'
            model.write_text(model.read_text().replace('/ a0','* a0',1))
            record=json.loads((run/'result.json').read_text());record['artifacts'][str(model.relative_to(run))]=sha(model)
            save(run/'result.json',record)
            with self.assertRaisesRegex(ValueError,'local-branch model does not match'):
                replay_run(run,root/'tampered')


if __name__=='__main__':
    unittest.main()
