"""Full-module admission, source selection controls and portable delivery."""
import io
import json
import os
import subprocess
import sys
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

from numerics.frontend import Unsupported,execute,parse
from numerics.delivery import pack,unpack,recheck
from numerics.workflow import ROOT,certify,prepare,replay_run,save,sha
from bootstrap_numerics import bootstrap,unpack_elan


CASES=ROOT/'benchmarks/numerics/heldout'


class DeliveryAdmissionTests(unittest.TestCase):
    def test_frozen_requirements_and_original_files_survive_assistance(self):
        for case in sorted(p for p in CASES.iterdir() if p.is_dir()):
            provenance=json.loads((case/'provenance.json').read_text())
            for name,digest in provenance['files'].items():self.assertEqual(sha(case/name),digest)
            original=json.loads((case/'initial-request.json').read_text());current=json.loads((case/'request.json').read_text())
            self.assertEqual(original,{k:v for k,v in current.items() if k not in ('cpp_module','python_module')})
            self.assertEqual(sha(case/'initial-request.json'),json.loads((case/'first-attempt.json').read_text())['request_sha256'])
            _,_,program,questions=prepare(case/'request.json')
            self.assertFalse(questions);self.assertTrue(program.selection)

    def test_python_selection_preserves_original_schedule_and_rejects_rebinding(self):
        source='import unused\ndef helper(x):\n    return x+1.0\ndef run(x):\n    return helper(x)*2.0\n'
        program=parse('python',source,'run',python_module=True)
        self.assertEqual(execute(program,[2.]),(6.,))
        for extra in ['run = other','if flag:\n    def run(x):\n        return x','if flag:\n    del helper','from other import helper']:
            with self.subTest(extra=extra),self.assertRaises(Unsupported):
                parse('python',source+extra+'\n','run',python_module=True)
        with self.assertRaises(Unsupported):parse('python',source.replace('def run','@decorator\ndef run'),'run',python_module=True)
        self.assertNotIn('selection',parse('python','def f(x):\n    return x\n','f').record())

    def test_original_crlf_source_keeps_its_frozen_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);source=b'import unused\r\ndef f(x):\r\n    return x+1.0\r\n'
            (root/'source.py').write_bytes(source)
            save(root/'request.json',{'schema':'numerics-request-v1','source':'source.py','function':'f','python_module':True})
            _,_,program,_=prepare(root/'request.json')
            self.assertEqual(program.selection['source_sha256'],sha(root/'source.py'))
            self.assertEqual(program,parse('python',source.decode(),'f',python_module=True))

    def test_cpp_constants_scope_and_preprocessing_are_explicit(self):
        source='namespace angles { inline double convert(double x) { return x*M_PI/180.0; } }'
        config={'constants':{'M_PI':'0x400921fb54442d18'}}
        p=parse('cpp',source,'angles::convert',cpp_module=config)
        self.assertEqual(execute(p,[180.]),(3.141592653589793,))
        self.assertEqual(p.selection['byte_range'][1],source.index(' }')+2)
        for changed in ['#define M_PI 3.0\n'+source,source.replace('double x','double *x'),
                        source.replace('return x*','throw x; return x*'),source.replace('inline double','template<class T=double> double'),source+source]:
            with self.subTest(changed=changed),self.assertRaises(Unsupported):parse('cpp',changed,'angles::convert',cpp_module=config)
        with self.assertRaises(Unsupported):parse('cpp',source,'convert',cpp_module=config)
        with self.assertRaises(Unsupported):parse('cpp',source,'angles::convert')

    def test_numpy_exact_integer_promotions_keep_large_integers_closed(self):
        source='import numpy as np\ndef f(x):\n    return (x*2+1)/4\n'
        p=parse('python',source,'f',scientific_arrays={'x':[2]})
        self.assertEqual(execute(p,[1.,2.]),(.75,1.25))
        with self.assertRaises(Unsupported):parse('python',source.replace('*2','*9007199254740993'),'f',scientific_arrays={'x':[2]})

    def test_bundle_rejects_traversal_and_links_without_writing_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            for index,name in enumerate(['../escape','/absolute','run/./x','run\\x','run/link']):
                archive=root/f'{index}.tar'
                with tarfile.open(archive,'w') as stream:
                    member=tarfile.TarInfo(name)
                    if name=='run/link':member.type=tarfile.SYMTYPE;member.linkname='/tmp/escape'
                    stream.addfile(member,io.BytesIO())
                with self.assertRaises(ValueError):unpack(archive,root/f'out{index}')
                self.assertFalse((root/f'out{index}').exists())

    def test_cli_retains_unsupported_admission_without_a_success_result(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);(root/'source.py').write_text('import math\ndef f(x):\n    return math.sin(x)\n')
            save(root/'request.json',{'schema':'numerics-request-v1','source':'source.py','function':'f'})
            result=subprocess.run([sys.executable,str(ROOT/'scripts/certify_numerics.py'),'run',
                '--request',str(root/'request.json'),'--out',str(root/'run')],capture_output=True,text=True)
            self.assertEqual(result.returncode,2)
            self.assertEqual(json.loads(result.stdout)['failure_kind'],'unsupported_source_or_profile')
            admission=json.loads((root/'run/admission.json').read_text())
            self.assertEqual((root/'run'/admission['frozen_source']).read_bytes(),(root/'source.py').read_bytes())
            self.assertEqual((root/'run/original-request.json').read_bytes(),(root/'request.json').read_bytes())
            self.assertFalse((root/'run/result.json').exists())

    def test_bootstrap_requires_matching_skill_before_any_download(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);skill=root/'SKILL.md';skill.write_text('wrong')
            with patch('bootstrap_numerics.Runner.run',side_effect=AssertionError('download called')):
                with self.assertRaisesRegex(ValueError,'Skill/provider mismatch'):bootstrap(ROOT,root/'tools',root/'out',skill=skill)
                with self.assertRaisesRegex(ValueError,'finite and positive'):bootstrap(ROOT,root/'tools',root/'out',timeout=float('nan'))


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION')=='1','Run make numerics-check')
class DeliveryLeanTests(unittest.TestCase):
    def test_heldout_sources_certify_portable_replay_and_stale_contract_rejection(self):
        parent=ROOT/'.cache/numerics-generated';parent.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='heldout-',dir=parent) as directory:
            root=Path(directory)
            for case in sorted(p for p in CASES.iterdir() if p.is_dir()):
                with self.subTest(case=case.name):
                    run=root/case.name;result=certify(case/'request.json',run)
                    self.assertEqual(result['status'],'certified',result.get('error'))
                    archive=root/(case.name+'.tar.gz');pack(run,archive)
                    moved=root/(case.name+'-moved');unpack(archive,moved)
                    with patch('numerics.runtimes.admit_runtime',side_effect=AssertionError('runtime called')):
                        checked=recheck(moved,case/'request.json',root/(case.name+'-replay'))
                    self.assertEqual(checked['status'],'rechecked')
                    timed=json.loads((case/'request.json').read_text())
                    timed.update(source=str(case/timed['source']),timeout_seconds=180)
                    save(root/'timed.json',timed)
                    timed_result=recheck(moved,root/'timed.json',root/(case.name+'-timed'))
                    self.assertEqual(timed_result['status'],'rechecked')
                    command=json.loads((root/(case.name+'-timed')/'replay/runs/lean-proof/run.json').read_text())
                    self.assertEqual(command['timeout_seconds'],180)
                    with patch('numerics.delivery.replay_run',side_effect=RuntimeError('rejected current proof')):
                        rejected=recheck(moved,case/'request.json',root/(case.name+'-rejected'))
                    self.assertEqual(rejected['status'],'unresolved')
                    self.assertEqual(json.loads((root/(case.name+'-rejected')/'recheck.json').read_text())['status'],'unresolved')
                    request=json.loads((case/'request.json').read_text());request['source']=str(case/request['source'])
                    request['outputs'][0]['limit']='1/10000000000000'
                    save(root/'changed.json',request)
                    changed=recheck(moved,root/'changed.json',root/(case.name+'-stale'))
                    self.assertEqual(changed['status'],'needs_reverification')
                    self.assertIn('contract or profile',changed['incompatible_changes'])
                    current=json.loads((case/'request.json').read_text())
                    changed_source=root/(case.name+'-changed-source'+Path(current['source']).suffix)
                    changed_source.write_bytes((case/current['source']).read_bytes()+b'\n')
                    current['source']=str(changed_source);save(root/'changed-source.json',current)
                    stale=recheck(moved,root/'changed-source.json',root/(case.name+'-source-stale'))
                    self.assertEqual(stale['status'],'needs_reverification')
                    self.assertIn('source',stale['incompatible_changes'])
