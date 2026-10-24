"""Explicit single-rounding FMA: source admission, checked bounds and frozen replay."""
from fractions import Fraction as Q
import json
import math
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from numerics import scalar
from numerics.emit import expression
from numerics.frontend import Unsupported, execute, parse
from numerics.integration import ARITHMETIC, EXPLICIT_FMA_ARITHMETIC, Session, ToolError, validate
from numerics.runtimes import admit_math
from numerics.workflow import ROOT, certify, prepare, replay_run, save


SOURCE = 'import math\ndef f(x, y, z):\n    return math.fma(x,y,z)\n'
HAS_RUNTIME = sys.implementation.name == 'cpython' and sys.version_info[:2] in ((3,13),(3,14)) and hasattr(math,'fma')
EXAMPLES = ROOT/'examples/numerics/fma'


class ExplicitFmaTests(unittest.TestCase):
    def test_profile_is_explicit_and_preserves_the_ternary_rounding_site(self):
        program = parse('python',SOURCE,'f',python_math=True)
        self.assertEqual([(n.op,n.args) for n in program.nodes],[('fma',('a0','a1','a2'))])
        self.assertEqual(program.record()['schema'],'ordered-binary64-explicit-fma-v1')
        self.assertEqual(expression(program.nodes[0]),'Float.fma a0 a1 a2')
        self.assertEqual(expression(program.nodes[0],ideal=True),'(a0 * a1 + a2)')
        with self.assertRaisesRegex(ValueError,'extraction bridge'):
            expression(program.nodes[0],rust=True)
        with self.assertRaises(Unsupported):
            parse('python',SOURCE,'f')
        plain = parse('python','def f(x,y,z):\n    return x*y+z\n','f')
        self.assertEqual([n.op for n in plain.nodes],['mul','add'])
        self.assertNotIn('math',plain.record())
        self.assertEqual(plain.record()['schema'],'ordered-binary64-v1')

    def test_imports_shadowing_casts_keywords_and_other_functions_are_closed(self):
        variants = [SOURCE.replace('import math','from math import fma'),
            SOURCE.replace('import math','import math as m'),
            SOURCE.replace('import math','import math, os'),
            SOURCE.replace('math.fma(x,y,z)','math.sin(x)'),
            SOURCE.replace('math.fma(x,y,z)','float(x)'),
            SOURCE.replace('math.fma(x,y,z)','math.fma(x,y,z=z)'),
            SOURCE.replace('math.fma(x,y,z)','math.fma(x,y)'),
            SOURCE.replace('f(x, y, z)','f(math, y, z)'),
            SOURCE.replace('return math.fma(x,y,z)','result = math.fma(x,y,z)\n    math = x\n    return result'),
            SOURCE.replace('import math','import math\nx = 1.0'),
            SOURCE.replace('math.fma(x,y,z)','x.fma(y,z)')]
        for source in variants:
            with self.subTest(source=source), self.assertRaises(Unsupported):
                parse('python',source,'f',python_math=True)
        for selector in [False,1,{'operations':['fma']}]:
            with self.assertRaises(Unsupported):
                parse('python',SOURCE,'f',python_math=selector)
        with self.assertRaises(Unsupported):
            parse('python',SOURCE,'f',python_math=True,python_branches=True)

    def test_helpers_and_literal_loops_retain_each_explicit_fma(self):
        source = 'import math\ndef step(x,y):\n    return math.fma(x,y,1.0)\ndef f(x,y):\n    for t in (1.0,2.0,3.0):\n        x = step(x,y)*t\n    return x\n'
        program = parse('python',source,'f',python_math=True)
        self.assertEqual(sum(n.op=='fma' for n in program.nodes),3)
        self.assertEqual(sum(n.op=='mul' for n in program.nodes),3)
        large = 'import math\ndef f(x):\n'+''.join('    x = math.fma(x,x,x)\n' for _ in range(33))+'    return x\n'
        with self.assertRaisesRegex(Unsupported,'32 IR nodes'):
            parse('python',large,'f',python_math=True)

    def test_wrong_formats_fusion_and_rounding_models_are_rejected(self):
        program = parse('python',SOURCE,'f',python_math=True)
        validate({},program)
        for model in [ARITHMETIC, {**EXPLICIT_FMA_ARITHMETIC,'fma':True},
                {**EXPLICIT_FMA_ARITHMETIC,'format':'binary32'},
                {**EXPLICIT_FMA_ARITHMETIC,'reassociation':True},
                {**EXPLICIT_FMA_ARITHMETIC,'rounding':'toward-zero'}]:
            with self.subTest(model=model), self.assertRaisesRegex(Unsupported,'arithmetic model'):
                validate({'arithmetic':model},program)
        plain=parse('python','def f(x,y,z):\n    return x*y+z\n','f')
        with self.assertRaisesRegex(Unsupported,'arithmetic model'):
            validate({'arithmetic':EXPLICIT_FMA_ARITHMETIC},plain)

    def test_external_producers_and_rust_require_separate_bridges(self):
        request,source,_,_=prepare(EXAMPLES/'calibrate.json')
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'request.json'
            for update in [{'producer':'gappa'},{'producer':'fptaylor'},{'producer':'precisa'},
                           {'target':'rust-aeneas'},{'proof':{'source':'unused.lean'}}]:
                save(path,{**request,'source':str(source),**update})
                with self.subTest(update=update), self.assertRaisesRegex(Unsupported,'Explicit FMA'):
                    prepare(path)

    def test_cancellation_and_nonpolynomial_operands_get_distinct_bounds(self):
        results={}
        for name in ['residual','separate_residual','reciprocal_calibrate']:
            request,_,program,_=prepare(EXAMPLES/(name+'.json'))
            candidate=scalar.proposal(program,request)
            results[name]=candidate.claims[program.outputs[0]].e
        self.assertLess(results['residual'],Q(1,10**23))
        self.assertGreater(results['separate_residual'],Q(1,10**23))
        self.assertLess(results['reciprocal_calibrate'],Q(1,10**13))

    def test_missing_runtime_wrong_version_and_hidden_two_rounding_steps_are_distinct(self):
        with patch('platform.python_implementation',return_value='PyPy'):
            with self.assertRaisesRegex(ToolError,'CPython'):
                admit_math({})
        with patch('numerics.runtimes.sys.version_info',(3,12,0)):
            with self.assertRaisesRegex(ToolError,'3.13 or 3.14'):
                admit_math({})
        with patch.object(math,'fma',None,create=True):
            with self.assertRaisesRegex(ToolError,'no fma'):
                admit_math({})
        with patch.object(math,'fma',lambda a,b,c:a*b+c,create=True):
            with self.assertRaisesRegex(ToolError,'preflight failed'):
                admit_math({})

    @unittest.skipUnless(HAS_RUNTIME,'Requires CPython 3.13/3.14 with math.fma')
    def test_actual_fma_and_separate_results_differ(self):
        program=parse('python',SOURCE,'f',python_math=True)
        x,y=1+2.0**-27,1-2.0**-27
        self.assertEqual(execute(program,[x,y,-1.0]),(-2.0**-54,))
        self.assertEqual(x*y-1.0,0.0)
        runtime={};admit_math(runtime)
        self.assertEqual(runtime['math_profile'],'python-math-fma-v1')
        self.assertTrue(runtime['libraries'][0]['files'])


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1' and HAS_RUNTIME,
                     'Run make numerics-check with CPython 3.13/3.14')
class ExplicitFmaLeanTests(unittest.TestCase):
    def test_kernels_certify_and_replay_without_runtime_or_inference(self):
        with tempfile.TemporaryDirectory(prefix='fma-tests-',dir=ROOT/'.cache/numerics-generated') as directory:
            root=Path(directory)
            for name in ['calibrate','residual','regularized_gain','fused_dot3','reciprocal_calibrate']:
                with self.subTest(kernel=name):
                    run=root/name
                    result=certify(EXAMPLES/(name+'.json'),run)
                    self.assertEqual(result['status'],'certified',result.get('error'))
                    obligation=json.loads((run/'obligation.json').read_text())
                    self.assertEqual(obligation['arithmetic'],EXPLICIT_FMA_ARITHMETIC)
                    evidence=json.loads((run/'evidence.json').read_text())
                    self.assertTrue(all(r['arithmetic']==EXPLICIT_FMA_ARITHMETIC for r in evidence['records']))
                    with patch.object(Session,'execute',side_effect=AssertionError('producer called')), \
                         patch('numerics.runtimes.admit_math',side_effect=AssertionError('runtime called')), \
                         patch('numerics.scalar.plan',side_effect=AssertionError('inference called')):
                        self.assertEqual(replay_run(run,root/(name+'-replay'))['status'],'replayed')

    def test_separate_schedule_keeps_its_strict_budget_and_reports_budget_not_met(self):
        with tempfile.TemporaryDirectory(prefix='fma-separate-',dir=ROOT/'.cache/numerics-generated') as directory:
            result=certify(EXAMPLES/'separate_residual.json',Path(directory)/'run')
            self.assertEqual(result['status'],'budget_not_met',result.get('error'))
            self.assertIn('lean_root_checked',result['completed_stages'])

    def test_zero_rounding_allowance_is_rejected_by_lean(self):
        with tempfile.TemporaryDirectory(prefix='fma-fault-',dir=ROOT/'.cache/numerics-generated') as directory:
            with patch('numerics.scalar.U',Q(0)):
                result=certify(EXAMPLES/'residual.json',Path(directory)/'run')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
            self.assertNotIn('lean_root_checked',result['completed_stages'])

    def test_substituting_separate_native_arithmetic_is_rejected_by_lean(self):
        original=scalar.expression
        def separate(node,ideal=False,**options):
            if node.op=='fma' and not ideal:
                a,b,c=node.args
                return f'({a} * {b} + {c})'
            return original(node,ideal=ideal,**options)
        with tempfile.TemporaryDirectory(prefix='fma-fault-',dir=ROOT/'.cache/numerics-generated') as directory:
            with patch('numerics.scalar.expression',side_effect=separate):
                result=certify(EXAMPLES/'residual.json',Path(directory)/'run')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
            self.assertNotIn('lean_root_checked',result['completed_stages'])
