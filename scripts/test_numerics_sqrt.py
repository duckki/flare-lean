"""Square-root source contracts, checked root evidence and cold replay controls."""
from dataclasses import replace
from fractions import Fraction as Q
import json
import math
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from numerics import scalar, square_root
from numerics.emit import expression
from numerics.frontend import Unsupported, execute, parse, word
from numerics.integration import ARITHMETIC, Session, ToolError, arithmetic, validate
from numerics.runtimes import admit_math, math_platform
from numerics.specification import lean_expression
from numerics.workflow import ROOT, audit_run, certify, prepare, replay_run, save, sha


SOURCE='import math\ndef f(x):\n    return math.sqrt(x)\n'
PROFILE={'schema':'python-math-sqrt-v1','operations':['sqrt']}
EXAMPLES=ROOT/'examples/numerics/sqrt'
HAS_RUNTIME=sys.implementation.name=='cpython' and sys.version_info[:2] in ((3,13),(3,14))


class SqrtInferenceTests(unittest.TestCase):
    def test_root_endpoints_are_exact_rational_evidence_without_host_sqrt(self):
        with patch.object(math,'sqrt',side_effect=AssertionError('host sqrt used')):
            for value in [Q(0),Q(1,3),Q(2),Q(4),Q(2)**-1074,Q(2)**1000]:
                lo,hi=square_root.endpoints(value)
                self.assertLessEqual(Q(0),lo)
                self.assertLessEqual(lo*lo,value)
                self.assertLessEqual(value,hi*hi)
            self.assertEqual(square_root.endpoints(4),(Q(2),Q(2)))
        with self.assertRaisesRegex(ValueError,'nonnegative'):
            square_root.endpoints(-1)

    def test_source_and_reference_select_distinct_primitive_semantics(self):
        program=parse('python',SOURCE,'f',python_math=True)
        self.assertEqual(program.math,PROFILE)
        self.assertEqual(program.record()['schema'],'ordered-binary64-sqrt-v1')
        self.assertEqual([(n.op,n.args) for n in program.nodes],[('sqrt',('a0',))])
        self.assertEqual(expression(program.nodes[0]),'Float.sqrt a0')
        self.assertEqual(expression(program.nodes[0],ideal=True),'Real.sqrt a0')
        self.assertEqual(lean_expression('sqrt(x)',('x',),allow_sqrt=True),'(Real.sqrt a0)')
        with self.assertRaises(ValueError):
            lean_expression('sqrt(x)',('x',))
        with self.assertRaisesRegex(ValueError,'extraction bridge'):
            expression(program.nodes[0],rust=True)
        for reference in ['math.sqrt(x)','sqrt(x,1)','sqrt(x=x)','sqrt(__import__("os"))']:
            with self.subTest(reference=reference),self.assertRaises(ValueError):
                lean_expression(reference,('x',),allow_sqrt=True)

    def test_source_aliases_shadowing_casts_keywords_and_other_calls_are_rejected(self):
        for source in [SOURCE.replace('import math','from math import sqrt'),
                SOURCE.replace('import math','import math as m'),
                SOURCE.replace('math.sqrt(x)','math.sqrt(x=x)'),
                SOURCE.replace('math.sqrt(x)','math.sqrt(x,1.0)'),
                SOURCE.replace('math.sqrt(x)','math.sin(x)'),
                SOURCE.replace('math.sqrt(x)','math.sqrt(float(x))'),
                SOURCE.replace('f(x)','f(math)'),
                SOURCE.replace('return math.sqrt(x)','result = math.sqrt(x)\n    math = x\n    return result')]:
            with self.subTest(source=source),self.assertRaises(Unsupported):
                parse('python',source,'f',python_math=True)
        with self.assertRaises(Unsupported):
            parse('python',SOURCE,'f')

    def test_wrong_formats_models_and_implicit_fusion_are_rejected(self):
        program=parse('python',SOURCE,'f',python_math=True)
        model=arithmetic(program)
        self.assertIs(model['fma'],False)
        self.assertEqual(model['functions'],{'sqrt':'ieee754-binary64-nearest-even'})
        for wrong in [ARITHMETIC,{**model,'format':'binary32'},{**model,'fma':'explicit'},
                {**model,'functions':{'sqrt':'one-ulp-libm'}},{**model,'rounding':'toward-zero'}]:
            with self.subTest(model=wrong),self.assertRaisesRegex(Unsupported,'arithmetic model'):
                validate({'arithmetic':wrong},program)
        fma=parse('python','import math\ndef f(x,y,z):\n    return math.fma(x,y,z)\n','f',python_math=True)
        self.assertEqual(fma.math,{'schema':'python-math-fma-v1','operations':['fma']})
        self.assertEqual(fma.record()['schema'],'ordered-binary64-explicit-fma-v1')
        self.assertNotIn('functions',arithmetic(fma))

    def test_positive_floor_and_zero_inclusive_rules_retain_incoming_error(self):
        for name in ['standard_deviation','regularized_norm','nested_root','fused_norm']:
            request,_,program,_=prepare(EXAMPLES/(name+'.json'))
            candidate=scalar.proposal(program,request)
            roots=[n for n in candidate.steps[0]['nodes'] if n['op']=='sqrt']
            if name=='standard_deviation':
                self.assertEqual(roots[0]['sqrt']['rule'],'squared-allowance')
                self.assertEqual(Q(roots[0]['sqrt']['incoming_allowance']),0)
            elif name=='nested_root':
                self.assertGreater(Q(roots[1]['sqrt']['incoming_allowance']),Q(1,10**9))
                self.assertEqual(roots[1]['sqrt']['rule'],'squared-allowance')
            else:
                self.assertEqual(roots[0]['sqrt']['rule'],'positive-floor')
                self.assertGreater(Q(roots[0]['sqrt']['incoming_allowance']),0)
            self.assertLess(candidate.claims[program.outputs[0]].e,Q(request['outputs'][0]['limit']))
        with self.assertRaisesRegex(ValueError,'nonnegative native and exact'):
            scalar.analyze_box(parse('python',SOURCE,'f',python_math=True),{'x':['-1','1']})

    def test_external_producers_and_rust_need_their_own_function_bridges(self):
        request,source,_,_=prepare(EXAMPLES/'standard_deviation.json')
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'request.json'
            for update in [{'producer':p} for p in ['gappa','fptaylor','precisa']]+[{'target':'rust-aeneas'}]:
                save(path,{**request,'source':str(source),**update})
                with self.subTest(update=update),self.assertRaisesRegex(Unsupported,'Square-root profile'):
                    prepare(path)

    @unittest.skipUnless(HAS_RUNTIME,'Requires selected CPython runtime')
    def test_runtime_contract_and_identity_do_not_require_unused_fma(self):
        with patch.object(math,'fma',None,create=True):
            runtime={};admit_math(runtime,PROFILE)
        self.assertEqual(runtime['math_profile'],PROFILE['schema'])
        self.assertEqual(runtime['platform'],math_platform())
        self.assertIn('sqrt',runtime['primitive_contracts'])
        program=parse('python',SOURCE,'f',python_math=True)
        for value in [-0.0,0.0,float.fromhex('0x1p-1074'),2.0,16.0]:
            self.assertEqual(word(execute(program,[value])[0]),word(math.sqrt(value)))
        with patch.object(math,'sqrt',None):
            with self.assertRaisesRegex(ToolError,'no sqrt'):
                admit_math({},PROFILE)
        with patch.object(math,'sqrt',lambda x:x):
            with self.assertRaisesRegex(ToolError,'preflight failed'):
                admit_math({},PROFILE)
        with patch('numerics.runtimes.sys.version_info',(3,15,0)):
            with self.assertRaisesRegex(ToolError,'3.13 or 3.14'):
                admit_math({},PROFILE)


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1' and HAS_RUNTIME,
                     'Run make numerics-check with CPython 3.13/3.14')
class SqrtLeanTests(unittest.TestCase):
    def request(self,root,name='standard_deviation',**updates):
        request,source,_,_=prepare(EXAMPLES/(name+'.json'))
        path=root/'request.json';save(path,{**request,'source':str(source),**updates})
        return path

    def test_applications_and_frozen_replay_without_runtime_or_inference(self):
        with tempfile.TemporaryDirectory(prefix='sqrt-applications-',dir=ROOT/'.cache/numerics-generated') as directory:
            root=Path(directory)
            for name in ['standard_deviation','regularized_norm','normalized_residual','fused_norm','nested_root']:
                with self.subTest(application=name):
                    run=root/name;result=certify(EXAMPLES/(name+'.json'),run)
                    self.assertEqual(result['status'],'certified',result.get('error'))
                    self.assertTrue(all(o['evidence']=='checked' for o in result['outputs']))
                    evidence=json.loads((run/'analysis.json').read_text())
                    self.assertIn('Flare.Binary64.SqrtPropagation.native_sqrt',evidence['producer_details']['primitive_rules'])
                    with patch.object(Session,'execute',side_effect=AssertionError('producer called')), \
                         patch('numerics.square_root.analyze',side_effect=AssertionError('inference called')), \
                         patch('numerics.runtimes.admit_math',side_effect=AssertionError('runtime called')), \
                         patch('numerics.runtimes.math_platform',side_effect=AssertionError('platform queried')):
                        self.assertEqual(replay_run(run,root/(name+'-replay'))['status'],'replayed')

    def test_zero_subnormal_and_rational_input_domains(self):
        with tempfile.TemporaryDirectory(prefix='sqrt-domains-',dir=ROOT/'.cache/numerics-generated') as directory:
            root=Path(directory)
            for index,bounds in enumerate([['0','0'],[str(Q(2)**-1074),str(Q(2)**-1074)],['1/3','2/3']]):
                request=self.request(root,domain={'variance':bounds})
                result=certify(request,root/str(index))
                self.assertEqual(result['status'],'certified',result.get('error'))
                self.assertEqual(replay_run(root/str(index),root/(str(index)+'-replay'))['status'],'replayed')

    def test_helper_pair_and_fma_after_square_root(self):
        with tempfile.TemporaryDirectory(prefix='sqrt-pair-',dir=ROOT/'.cache/numerics-generated') as directory:
            root=Path(directory)
            source=root/'kernel.py'
            source.write_text('import math\ndef root(x):\n    return math.sqrt(x)\n'
                              'def f(x):\n    r = root(x)\n    return -r, math.fma(2.0,r,x)\n')
            request=self.request(root,source=str(source),function='f',domain={'x':['1','4']},
                specification=['-sqrt(x)','2*sqrt(x)+x'],outputs=[
                    {'name':name,'unit':'1','limit':'1/1000000000000'} for name in ['negative_root','affine']])
            result=certify(request,root/'run')
            self.assertEqual(result['status'],'certified',result.get('error'))
            self.assertEqual(len(result['outputs']),2)
            self.assertEqual(replay_run(root/'run',root/'replay')['status'],'replayed')

    def test_invalid_radicand_and_checked_budget_miss_are_distinct(self):
        with tempfile.TemporaryDirectory(prefix='sqrt-domains-',dir=ROOT/'.cache/numerics-generated') as directory:
            root=Path(directory)
            bad=self.request(root,domain={'variance':['-1','16']})
            result=certify(bad,root/'negative')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','analysis'))
            self.assertIn('nonnegative native and exact',result['error'])
            tight=self.request(root,outputs=[{'name':'standard_deviation','unit':'1','limit':str(Q(2)**-60)}])
            result=certify(tight,root/'tight')
            self.assertEqual(result['status'],'budget_not_met',result.get('error'))
            self.assertIn('lean_root_checked',result['completed_stages'])
            self.assertEqual(replay_run(root/'tight',root/'tight-replay')['certificate_status'],'budget_not_met')

    def test_bad_endpoints_incoming_error_and_native_primitive_fail_in_lean(self):
        original=square_root.analyze
        def bad_endpoint(*args,**options):
            bound,meta=original(*args,**options)
            return bound,{**meta,'upper':meta['upper']/2}
        def lost_error(*args,**options):
            bound,meta=original(*args,**options)
            return replace(bound,e=meta['rounding_allowance']),{**meta,'incoming_allowance':Q(0)}
        original_expression=scalar.expression
        def wrong_primitive(node,ideal=False,**options):
            if node.op=='sqrt' and not ideal:return node.args[0]
            return original_expression(node,ideal=ideal,**options)
        with tempfile.TemporaryDirectory(prefix='sqrt-faults-',dir=ROOT/'.cache/numerics-generated') as directory:
            root=Path(directory)
            for label,name,context in [('endpoint','standard_deviation',patch('numerics.square_root.analyze',side_effect=bad_endpoint)),
                    ('incoming-error','regularized_norm',patch('numerics.square_root.analyze',side_effect=lost_error)),
                    ('primitive','standard_deviation',patch('numerics.scalar.expression',side_effect=wrong_primitive))]:
                with context:
                    result=certify(EXAMPLES/(name+'.json'),root/label)
                self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
                self.assertNotIn('lean_root_checked',result['completed_stages'])
            request=self.request(root,specification=['sqrt(variance+1)'])
            result=certify(request,root/'reference')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-proof'))

    def test_platform_and_library_freshness_are_checked_without_weakening_replay(self):
        with tempfile.TemporaryDirectory(prefix='sqrt-identity-',dir=ROOT/'.cache/numerics-generated') as directory:
            root=Path(directory);run=root/'run'
            result=certify(EXAMPLES/'standard_deviation.json',run)
            self.assertEqual(result['status'],'certified',result.get('error'))
            runtime=json.loads((run/'source-runtime.json').read_text())
            libraries=set(runtime['libraries'][0]['files'])
            with patch('numerics.runtimes.math_platform',return_value={'system':'changed'}):
                with self.assertRaisesRegex(ValueError,'math platform changed'):
                    audit_run(run,frozen=False)
            with patch('numerics.workflow.sha',side_effect=lambda p:'0'*64 if str(p) in libraries else sha(p)):
                with self.assertRaisesRegex(ValueError,'runtime library changed'):
                    audit_run(run,frozen=False)
            self.assertEqual(replay_run(run,root/'replay')['status'],'replayed')
