"""Bounded source semantics, independent recurrence contracts and scale fixtures."""
import gzip
import ast
import json
import tempfile
from pathlib import Path
import unittest

from numerics.analysis import analyze
from numerics.frontend import FRONTENDS,Unsupported,execute,parse,word
from numerics.scale import load_graph,probe
from numerics.specification import validate
from numerics.workflow import ROOT,prepare
from benchmark_numerics import matches


class BoundedPythonTests(unittest.TestCase):
    def test_helpers_and_tuple_iteration_preserve_original_words_and_scope(self):
        source='''def advance(x, y):
    local = x + y
    return local, x - y
def run(x, y, z):
    for observation in (y, z):
        x, y = advance(x, observation)
    return x, y
'''
        program=parse('python',source,'run')
        function=FRONTENDS['python'].load_for_diagnostics(source,'run')
        for args in [(1e16,-1e16,1.0),(-0.0,0.0,-0.0),(1.0,2.0,3.0)]:
            self.assertEqual(tuple(map(word,execute(program,args))),tuple(map(word,function(*args))))

    def test_recursion_dynamic_loops_control_flow_and_effects_are_rejected(self):
        sources=['def f(x):\n    return f(x)\n',
                 'def f(x):\n    return g(x)\ndef g(x):\n    return f(x)\n',
                 'def f(x):\n    for y in x:\n        x += y\n    return x\n',
                 'def f(x):\n    for y in range(4):\n        x += y\n    return x\n',
                 'def f(x):\n    for y in (x, x):\n        break\n    return x\n',
                 'def f(x):\n    for y in (x, x):\n        return y\n    return x\n',
                 'def f(x):\n    return g(x, x)\ndef g(x):\n    return x\n',
                 'def f(x):\n    return print(x)\n',
                 'def float(x):\n    return x\ndef f(x):\n    return x\n']
        for source in sources:
            with self.subTest(source=source),self.assertRaises(Unsupported):parse('python',source,'f')

    def test_bounded_expansion_has_a_work_limit(self):
        values=', '.join(['x']*128)
        source=f'def f(x):\n    for a in ({values}):\n        for b in ({values}):\n            x += a\n    return x\n'
        with self.assertRaisesRegex(Unsupported,'work limit'):parse('python',source,'f')

    def test_node_limit_also_covers_the_final_return_expression(self):
        outer=', '.join(['x']*128)
        inner=', '.join(['x']*78)
        tail=', '.join(['x']*15)
        # The loops emit 9,999 nodes; the final expression adds two more.
        source=f'def f(x):\n    for a in ({outer}):\n        for b in ({inner}):\n            x += a\n    for c in ({tail}):\n        x += c\n    return x + x + x\n'
        with self.assertRaisesRegex(Unsupported,'work limit'):parse('python',source,'f')

    def test_later_local_binding_cannot_masquerade_as_a_global_helper_call(self):
        source='''def advance(x):
    return x + x
def run(x):
    for value in (advance(x), x):
        advance = value
    return x
'''
        with self.assertRaisesRegex(Unsupported,'unshadowed'):parse('python',source,'run')


class ScaleFixtureTests(unittest.TestCase):
    def test_loop_work_and_independent_inputs_scale_with_the_horizon(self):
        for family in ['kalman','imu']:
            for count in [1,4,16,48]:
                request,_,program,questions=prepare(ROOT/'examples/numerics/scale'/f'{family}_{count:03d}.json')
                self.assertEqual(questions,[])
                self.assertEqual(sum(n.op!='constant' for n in program.nodes),8*count)
                self.assertEqual(len(program.inputs),count+(4 if family=='kalman' else 3))
                self.assertEqual(len(request['specification']['sequence']),count)

    def test_scale_helpers_preserve_the_imported_operation_schedule(self):
        for family,original in [('kalman','scalar_kalman.py'),('imu','imu_prediction.py')]:
            base=ast.parse((ROOT/'examples/numerics'/original).read_text()).body[0]
            scaled=ast.parse((ROOT/'examples/numerics/scale'/(family+'_loop.py')).read_text()).body[0]
            self.assertEqual(ast.dump(base),ast.dump(scaled))

    def test_checked_ideal_refinement_keeps_repeated_kalman_analysis_usable(self):
        request,_,program,_=prepare(ROOT/'examples/numerics/scale/kalman_016.json')
        bounds,steps=analyze(program,request['domain'])
        self.assertTrue(any(s['ideal_refinement'] for s in steps))
        self.assertLess(float(bounds[program.outputs[0]].e),1e-4)

    def test_unresolved_scale_case_has_the_intended_analysis_failure(self):
        request,_,program,_=prepare(ROOT/'examples/numerics/scale/kalman_128.json')
        with self.assertRaisesRegex(ValueError,'denominator'):analyze(program,request['domain'])

    def test_fold_validation_rejects_unknown_inputs_and_ambiguous_state_names(self):
        request,_,program,_=prepare(ROOT/'examples/numerics/scale/kalman_004.json')
        spec=request['specification']
        for change in [{'sequence':['unknown']},{'state':['mean','p']},{'step':['m','unknown']}]:
            with self.subTest(change=change),self.assertRaises(ValueError):validate({**spec,**change},program)

    def test_partial_expression_specifications_still_request_missing_information(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);(root/'source.py').write_text('def f(x):\n    return x, x\n')
            request={'schema':'numerics-request-v1','source':'source.py','function':'f',
                     'domain':{'x':['-1','1']},'outputs':[{'name':n,'unit':'m','limit':'1'} for n in ['a','b']],
                     'specification':['x']}
            (root/'request.json').write_text(json.dumps(request))
            _,_,_,questions=prepare(root/'request.json')
            self.assertEqual([q['field'] for q in questions],['specification'])

    def test_original_large_graphs_are_retained_and_only_probed(self):
        for label,count in [('relative',7758),('global',7761)]:
            path=ROOT/'benchmarks/numerics/scale'/(label+'-graph.json.gz')
            original=json.loads(gzip.decompress(path.read_bytes()))
            self.assertEqual(len(original['nodes']),count)
            _,_,_,metrics=load_graph(path,['accepted_displacement','accepted_variance'])
            self.assertEqual(metrics['arithmetic_operations'],count)
            result=probe(path,['accepted_displacement','accepted_variance'])
            self.assertEqual(result['status'],'candidate_only')
            self.assertIsNone(result['entry_theorem'])

    def test_matching_an_expected_gap_requires_the_right_reason(self):
        case={'expected':'unresolved','expected_failure_stage':'analysis','expected_error_contains':'denominator'}
        self.assertTrue(matches(case,{'status':'unresolved','failure_stage':'analysis','error':'lost denominator'}))
        self.assertFalse(matches(case,{'status':'unresolved','failure_stage':'lean-proof','error':'timeout'}))
        limited={'expected':'certified','resource_limits_allowed':True}
        self.assertTrue(matches(limited,{'status':'unresolved','failure_stage':'lean-proof','failure_kind':'heartbeats'}))
        self.assertFalse(matches(limited,{'status':'unresolved','failure_stage':'lean-proof','failure_kind':'stage_rejected'}))


if __name__=='__main__':unittest.main()
