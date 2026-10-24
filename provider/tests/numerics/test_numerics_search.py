"""Untrusted CBMC traces, explicit property routing and genuine witness checking."""
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from numerics.workflow.search import endpoint, harness, witness
from numerics.frontends.scalar import Unsupported, parse
from numerics.workflow.certification import ROOT, certify, prepare, replay_run, save


class SearchAdmissionTests(unittest.TestCase):
    def test_trace_requires_one_visible_exact_original_word_per_input(self):
        trace=[{'stepType':'assignment','lhs':'flare_input_bits0','hidden':True,'value':{'binary':'0'*64,'width':64}},
               {'stepType':'assignment','lhs':'flare_input_bits0','value':{'binary':'0'*63+'1','width':64}}]
        def record(steps):return json.dumps([{'result':[{'property':'main.assertion.1','status':'FAILURE','trace':steps}]}])
        self.assertEqual(witness(record(trace),['x']),{'x':'0x0000000000000001'})
        for steps in [trace[:1],trace+[trace[1]],[{**trace[1],'value':{'binary':'0'*64,'width':32}}]]:
            with self.assertRaises(ValueError):witness(record(steps),['x'])
        with self.assertRaises(ValueError):witness('[]',['x'])
        with self.assertRaises(ValueError):witness(record(trace).replace('FAILURE','SUCCESS'),['x'])

    def test_actual_retained_cpp_trace_matches_the_maintained_witness(self):
        case=ROOT/'benchmarks/numerics/heldout/ros-angles'
        words=witness((case/'cbmc-trace.json').read_text(),['degrees'])
        expected=json.loads((case/'positivity_witness.json').read_text())
        self.assertEqual(words,expected['counterexample']['inputs'])
        self.assertEqual(prepare(case/'positivity_witness.json')[2],prepare(case/'positivity_search.json')[2])

    def test_search_does_not_change_reference_domain_or_rounding_schedule(self):
        p=parse('python','def f(x):\n    return (x*3.0)/180.0\n','f')
        request={'domain':{'x':['1/10','2']},'counterexample_search':{'output':0}}
        source=harness(p,request)
        self.assertLess(source.index('a0 * n0'),source.index('n1 / n2'))
        self.assertIn('assert(n3 > 0.0)',source)
        from fractions import Fraction as Q
        self.assertGreaterEqual(Q.from_float(float.fromhex(endpoint('1/10',True))),Q(1,10))
        self.assertLessEqual(Q.from_float(float.fromhex(endpoint('1/10',False))),Q(1,10))
        self.assertGreater(float.fromhex(endpoint('1/'+str(2**2000),True)),0.)

    def test_missing_tool_is_retained_and_never_a_certificate(self):
        parent=ROOT/'.cache/numerics-generated';parent.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='search-missing-',dir=parent) as directory:
            root=Path(directory);(root/'source.py').write_text('def f(x):\n    return x/180.0\n')
            save(root/'request.json',{'schema':'numerics-request-v1','source':'source.py','function':'f',
                'domain':{'x':['1/100','1']},'specification':['x/180'],
                'outputs':[{'name':'out','unit':'1','property':'strict_positive'}],
                'counterexample_search':{'tool':'cbmc','output':0},'search_tools':{'cbmc':{'path':str(root/'missing')}}})
            result=certify(root/'request.json',root/'run')
            self.assertEqual((result['status'],result['failure_kind']),('unresolved','missing_tool'))
            self.assertEqual(result['failure_stage'],'cbmc-admission')
            self.assertEqual(json.loads((root/'run/evidence.json').read_text())['selected_witness_proposer'],'cbmc')
            with self.assertRaises(ValueError):replay_run(root/'run',root/'replay')


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1' and os.environ.get('FLARE_CBMC'),'Optional pinned CBMC 6.11.0')
class SearchLeanTests(unittest.TestCase):
    def test_real_search_witness_checks_and_replays_without_search_tool(self):
        parent=ROOT/'.cache/numerics-generated';parent.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='cbmc-',dir=parent) as directory:
            root=Path(directory);(root/'source.py').write_text('def f(x):\n    return x/180.0\n')
            request={'schema':'numerics-request-v1','source':'source.py','function':'f',
                'domain':{'x':['1/'+str(2**1074),'1']},'specification':['x/180'],
                'outputs':[{'name':'out','unit':'1','property':'strict_positive'}],
                'counterexample_search':{'tool':'cbmc','output':0},'search_tools':{'cbmc':{'path':os.environ['FLARE_CBMC']}}}
            save(root/'request.json',request);result=certify(root/'request.json',root/'run')
            self.assertEqual(result['status'],'counterexample',result.get('error'))
            with patch('numerics.workflow.search.certify',side_effect=AssertionError('search invoked')), \
                 patch('numerics.runtimes.source.admit_runtime',side_effect=AssertionError('source invoked')):
                self.assertEqual(replay_run(root/'run',root/'replay')['status'],'replayed')
            (root/'identity.py').write_text('def f(x):\n    return x\n')
            request.update(source='identity.py',domain={'x':['1/100','1']},specification=['x'])
            save(root/'positive.json',request)
            positive=certify(root/'positive.json',root/'no-witness')
            self.assertEqual((positive['status'],positive['failure_kind']),('unresolved','no_witness'))
            self.assertNotIn('entry_theorem',positive)
