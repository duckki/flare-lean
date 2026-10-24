"""Conditional source semantics, PRECiSA admission and independent Lean checking."""
from fractions import Fraction as Q
import json
import math
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

from numerics.integrations.adapter_precisa import PIN, endpoint, input_files, parse_result, receipt
from numerics.frontends.scalar import FRONTENDS, Unsupported, execute, parse, word
from numerics.integrations.registry import Session, ToolError, replay_evidence
from numerics.integrations.setup_precisa import FILIB_SHA, KODIAK, launcher
from numerics.workflow.certification import ROOT, audit_run, certify, prepare, replay_run, save, sha


EXAMPLES = ROOT/'examples/numerics/branches'


def output(stable=0, unstable=1):
    return {'results':[{'function':'kernel','stableError':stable,'unstableError':unstable}],
            'certFile':'analysis_cert.pvs','numCertFile':'analysis_num_cert.pvs'}


def fixture_tool(root):
    """A deliberately untrusted analyzer stand-in, never a real-tool acceptance test."""
    (root/'bin').mkdir(parents=True)
    (root/'libexec').mkdir()
    (root/'lib').mkdir()
    (root/'lib/libkodiak.so').write_bytes(b'fixture library')
    native = root/'libexec/precisa'
    native.write_text('#!'+sys.executable+'\nfrom pathlib import Path\nimport json\n'
        'for name in ["analysis_cert.pvs","analysis_num_cert.pvs"]:\n'
        '    Path(name).write_text("untrusted foreign trace\\n")\n'
        'print('+repr(json.dumps(output()))+')\n')
    native.chmod(0o755)
    wrapper = root/'bin/precisa'
    wrapper.write_text(launcher().replace('#!/usr/bin/env python3', '#!'+sys.executable))
    wrapper.chmod(0o755)
    save(root/'precisa-build.json', {'schema':'numerics-precisa-build-v1',
        'version':'4.0.4','source_revision':PIN['setup']['source']['revision'],
        'kodiak_revision':KODIAK,'filib_sha256':FILIB_SHA,'binary_sha256':sha(native),
        'library_sha256':{'libkodiak.so':sha(root/'lib/libkodiak.so')}})
    return {'executable':str(wrapper), 'base':str(root)}


class BranchAdmissionTests(unittest.TestCase):
    def test_original_source_and_graph_match_words_at_guard_endpoints(self):
        tiny = float.fromhex('0x0.0000000000001p-1022')
        for operator in ['<','<=','>','>=']:
            for else_form in ['else:\n        return -y', 'return -y']:
                source = ('def f(x: float, y: float) -> float:\n    x += 1.0\n'
                          '    if x '+operator+' y:\n        return -x\n    '+else_form+'\n')
                program = parse('python',source,'f',python_branches=True)
                function = FRONTENDS['python'].load_for_diagnostics(source,'f')
                for arguments in [(-1.0,0.0),(-1.0,-0.0),(tiny,1.0),(-2.0,-tiny),
                                  (-2**-54,1.0),(0.0,math.nextafter(1.0,2.0))]:
                    self.assertEqual(word(execute(program,arguments)[0]),word(function(*arguments)))
                self.assertEqual(program.nodes[-1].op, 'select_lt' if operator in ['<','>'] else 'select_le')

    def test_closed_profile_rejects_side_effects_nested_guards_and_incompatible_profiles(self):
        bodies = ['if x == 0.0:\n        return x\n    return -x',
                  'if 0.0 < x < 1.0:\n        return x\n    return -x',
                  'if x < 0.0:\n        y=x\n        return y\n    return -x',
                  'if x < 0.0:\n        return x, x\n    return -x',
                  'if x < 0.0:\n        return x\n    else:\n        return -x\n    x+=1.0',
                  'print(x)\n    if x < 0.0:\n        return x\n    return -x',
                  'if x < 0.0:\n        return abs(x)\n    return x',
                  'if x < 0.0:\n        if x < -1.0:\n            return x\n        return -x\n    return x']
        for body in bodies:
            with self.subTest(body=body), self.assertRaises(Unsupported):
                parse('python','def f(x):\n    '+body+'\n','f',python_branches=True)
        source = 'def f(x):\n    if x < 0.0:\n        return x\n    return -x\n'
        for updates in [{'python_branches':False}, {'python_branches':1},
                        {'python_branches':True,'python_arrays':{}},
                        {'python_branches':True,'python_method':{}}]:
            with self.subTest(updates=updates), self.assertRaises(Unsupported):
                parse('python',source,'f',**updates)
        with self.assertRaises(Unsupported):
            parse('python','import os\n'+source,'f',python_branches=True)
        self.assertNotIn('branches',parse('python','def f(x):\n    return x+x\n','f').record())

    def test_exporter_preserves_guard_and_encloses_decimal_domains(self):
        for exact in ['-1/10','1/10','1/3','-1/3',str(Q(2)**-1074),'0']:
            self.assertLessEqual(Q.from_float(float(endpoint(exact,True))),Q(exact))
            self.assertGreaterEqual(Q.from_float(float(endpoint(exact,False))),Q(exact))
        request,_,program,_ = prepare(EXAMPLES/'gate.json')
        source,ranges = input_files(program,request)
        self.assertIn('float_bounded_axiomatic@ieee754_double',source)
        self.assertIn('IF n2 <= n1 THEN n3 ELSE n4 ENDIF',source)
        self.assertNotIn('assume',source)
        self.assertIn('[-2.220446049250313e-16,2.220446049250313e-16]',ranges)
        from numerics.analysis.branches import proposal
        value = proposal(program, request)
        bound = value.summaries[program.outputs[0]]
        self.assertEqual((bound.c-bound.w,bound.c+bound.w,bound.i),(0,1,1))

    def test_precisa_candidates_round_trip_and_reject_invalid_summaries(self):
        record,stable,unstable = parse_result(json.dumps(output(0.1,1.0)))
        self.assertEqual(stable,Q.from_float(0.1))
        self.assertEqual(unstable,1)
        self.assertIsNone(parse_result(json.dumps(output(0,None)))[2])
        invalid = [output(-1,1),output(0,-1),output(True,1),output(0,float('nan')),
                   output(float('inf'),1),{**output(),'certFile':False},
                   {**output(),'results':[]},{**output(),'assumeStability':True}]
        wrong_function = output(); wrong_function['results'][0]['function']='unrelated'
        invalid.append(wrong_function)
        for record in invalid:
            with self.subTest(record=record), self.assertRaises(ValueError):
                parse_result(json.dumps(record))
        with self.assertRaisesRegex(ValueError,'Duplicate'):
            parse_result('{"results":[],"results":[]}')

    def test_build_receipt_binds_version_native_binary_and_backend(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory); chosen=fixture_tool(root)
            self.assertEqual(receipt(root/'bin/precisa',chosen),root.resolve())
            original=json.loads((root/'precisa-build.json').read_text())
            for field in ['schema','version','source_revision','kodiak_revision','filib_sha256','binary_sha256']:
                save(root/'precisa-build.json',{**original,field:'wrong'})
                with self.subTest(field=field),self.assertRaises(ToolError) as error:
                    receipt(root/'bin/precisa',chosen)
                self.assertEqual(error.exception.kind,'tool_identity_mismatch')
            for malformed in [[],{**original,'library_sha256':[]},{}]:
                save(root/'precisa-build.json',malformed)
                with self.assertRaises(ToolError):
                    receipt(root/'bin/precisa',chosen)
            save(root/'precisa-build.json',original)
            (root/'lib/libkodiak.so').write_bytes(b'changed library')
            with self.assertRaises(ToolError):
                receipt(root/'bin/precisa',chosen)


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1','Run make numerics-check')
class BranchLeanTests(unittest.TestCase):
    def request(self,root,example,**updates):
        request,source,_,_=prepare(EXAMPLES/example)
        save(root/'request.json',{**request,'source':str(source),**updates})
        return root/'request.json'

    def test_continuous_and_discontinuous_flows_certify_and_replay_without_inference(self):
        with tempfile.TemporaryDirectory(prefix='flare-branches-') as directory:
            root=Path(directory)
            for name in ['innovation_magnitude','gate']:
                run=root/name
                result=certify(self.request(root,name+'.json'),run)
                self.assertEqual(result['status'],'certified',result.get('error'))
                self.assertEqual(result['producer_validation'],'lean-conditional-four-flows-v1')
                with patch.object(Session,'execute',side_effect=AssertionError('producer called')), \
                     patch('numerics.analysis.branches.proposal',side_effect=AssertionError('inference called')):
                    self.assertEqual(replay_run(run,root/(name+'-replay'))['status'],'replayed')

    def test_precisa_evidence_is_used_and_false_stability_cannot_close_the_root(self):
        with tempfile.TemporaryDirectory(prefix='flare-precisa-check-') as directory:
            root=Path(directory); chosen=fixture_tool(root/'tool')
            request=self.request(root,'gate_precisa.json',analysis_tools={'precisa':chosen})
            run=root/'valid'; result=certify(request,run)
            self.assertEqual(result['status'],'certified',result.get('error'))
            self.assertEqual(Q(result['outputs'][0]['bound']),1)
            evidence=json.loads((run/'evidence.json').read_text())
            details=evidence['records'][0]['details']
            self.assertEqual((details['stable_candidate'],details['unstable_candidate']),('0','1'))
            self.assertFalse(details['assume_stability'])
            self.assertIn('actual maximum stable/unstable candidate',(run/'report.md').read_text())
            self.assertTrue(all('snapshot' not in d for d in evidence['tools'][0]['data_files'][1:]))
            for index,unstable in enumerate([None,Q(0)]):
                with patch('numerics.integrations.adapter_precisa.parse_result',return_value=(output(),Q(0),unstable)):
                    result=certify(request,root/('false-'+str(index)))
                self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
                self.assertNotIn('lean_root_checked',result['completed_stages'])
            with patch.object(Session,'tool',side_effect=AssertionError('tool called')), \
                 patch('numerics.integrations.registry.adapters',side_effect=AssertionError('registry called')):
                self.assertEqual(replay_run(run,root/'replay')['status'],'replayed')
            (run/'producer/analysis_cert.pvs').write_text('corrupted trace')
            with self.assertRaisesRegex(ValueError,'Changed|mismatch|stale'):
                audit_run(run,frozen=True)

    def test_wrong_exact_reference_and_resealed_domain_mismatch_are_rejected(self):
        with tempfile.TemporaryDirectory(prefix='flare-branch-reference-') as directory:
            root=Path(directory)
            request=self.request(root,'gate.json',specification=['1 if signal+1 >= 1 else 1'])
            result=certify(request,root/'wrong-reference')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
            request=self.request(root,'gate.json')
            run=root/'valid'; self.assertEqual(certify(request,run)['status'],'certified')
            frozen=json.loads((run/'obligation.json').read_text())
            frozen['program']['nodes'][-1]['op']='select_lt'
            save(run/'obligation.json',frozen)
            request,_,program,_=prepare(run/'request.json')
            with self.assertRaisesRegex(ValueError,'does not match'):
                replay_evidence(run,request,program)


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1' and os.environ.get('FLARE_PRECISA'),
                     'Set FLARE_PRECISA to the maintained real PRECiSA launcher')
class RealPrecisaTests(unittest.TestCase):
    def test_successful_analysis_with_forged_stability_still_fails_in_lean(self):
        with tempfile.TemporaryDirectory(prefix='flare-real-precisa-rejection-') as directory:
            root=Path(directory)
            request,source,_,_=prepare(EXAMPLES/'gate_precisa.json')
            save(root/'request.json',{**request,'source':str(source)})
            def false_stability(text):
                record,stable,_=parse_result(text)
                return record,stable,None
            with patch('numerics.integrations.adapter_precisa.parse_result',side_effect=false_stability):
                result=certify(root/'request.json',root/'false')
            self.assertEqual((result['status'],result['failure_stage']),('unresolved','lean-authored'))
            command=json.loads((root/'false/runs/precisa-analysis/run.json').read_text())
            self.assertEqual(command['returncode'],0,command)
            self.assertNotIn('lean_root_checked',result['completed_stages'])

    def test_real_branch_summaries_and_producer_free_replay(self):
        with tempfile.TemporaryDirectory(prefix='flare-real-precisa-') as directory:
            root=Path(directory)
            for name,expected in [('gate','certified'),('innovation_magnitude','budget_not_met')]:
                request,source,_,_=prepare(EXAMPLES/(name+'_precisa.json'))
                save(root/'request.json',{**request,'source':str(source)})
                run=root/name
                result=certify(root/'request.json',run)
                self.assertEqual(result['status'],expected,result.get('error'))
                details=json.loads((run/'evidence.json').read_text())['records'][0]['details']
                self.assertEqual(Q(result['outputs'][0]['bound']),
                    max(Q(details['stable_candidate']),Q(details['unstable_candidate'] or '0')))
                with patch.object(Session,'execute',side_effect=AssertionError('producer called')):
                    self.assertEqual(replay_run(run,root/(name+'-replay'))['status'],'replayed')


if __name__=='__main__':
    unittest.main()
