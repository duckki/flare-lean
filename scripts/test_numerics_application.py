"""Multi-module Rust contracts, full API checking and frozen Lean-only replay."""
import copy
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from numerics.workflow import ROOT, audit_run, certify, prepare, replay_run, save, sha
from numerics.application import check_extracted_files

FIXTURE = ROOT/'examples/numerics/imu48/request.json'


def selected_request():
    request = json.loads(FIXTURE.read_text())
    request['source'] = str((FIXTURE.parent/request['source']).resolve())
    for field in ('files', 'lean_modules'):
        request['rust_application'][field] = {
            name: str((FIXTURE.parent/source).resolve())
            for name, source in request['rust_application'][field].items()}
    return request


class ApplicationAdmissionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='flare-application-admission-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.request = selected_request()

    def prepare(self, request):
        save(self.root/'request.json', request)
        return prepare(self.root/'request.json')

    def test_actual_public_api_and_companion_are_selected_without_scalar_rewriting(self):
        _, source, program, questions = self.prepare(self.request)
        self.assertEqual(questions, [])
        self.assertEqual(source, ROOT/'benchmarks/numerics/scale/imu48.rs')
        self.assertEqual(program.function, 'imu_epoch::assess')
        self.assertIn('src/timestamp_alignment.rs', program.files)
        self.assertEqual(program.record()['profile'], 'rust-application-proof-v1')

    def test_reserved_modules_paths_and_incompatible_selectors_are_rejected(self):
        variants = []
        for path in ('../outside.rs', 'src/../outside.rs', '/src/absolute.rs', 'src//alias.rs'):
            request = copy.deepcopy(self.request)
            request['rust_application']['files'][path] = request['source']
            variants.append(request)
        for module in ('Workflow.Generated.Funs', 'Workflow.Check', 'Other.Proof'):
            request = copy.deepcopy(self.request)
            request['rust_application']['lean_modules'][module] = __file__
            variants.append(request)
        for field, value in [('domain', {}), ('producer', 'gappa'), ('target', 'lean'),
                             ('function', 'other'), ('timeout_seconds', float('nan')),
                             ('source_runtime', {'kind': 'rustc'})]:
            variants.append({**self.request, field: value})
        for request in variants:
            with self.subTest(request=request), self.assertRaises(ValueError):
                self.prepare(request)

    def test_unselected_source_and_incomplete_contract_are_rejected(self):
        for field in ('source', 'contract'):
            request = copy.deepcopy(self.request)
            if field == 'source':
                request['source'] = __file__
            else:
                del request['rust_application']['lean_modules']['Workflow.Contract']
            with self.assertRaises(ValueError):
                self.prepare(request)

    def test_profile_dispatch_preserves_invalid_schema_errors(self):
        for value in (None, True, [], 42):
            save(self.root/'invalid.json', value)
            with self.assertRaisesRegex(ValueError, 'Expected schema'):
                certify(self.root/'invalid.json', self.root/'unused')

    def test_companion_and_authored_contract_participate_in_freshness_audit(self):
        for label in ('companion.rs', 'contract.lean.txt'):
            run = self.root/label
            run.mkdir()
            source = run/'original.rs'
            source.write_text('original source')
            companion = run/label
            companion.write_text('original companion')
            save(run/'result.json', {'status': 'certified', 'artifacts': {},
                'source_path': str(source), 'source_sha256': sha(source),
                'application_inputs': [{'path': str(companion), 'sha256': sha(companion)}]})
            self.assertEqual(audit_run(run)['status'], 'fresh')
            companion.write_text('changed input')
            with self.assertRaisesRegex(ValueError, 'Application source, contract or proof changed'):
                audit_run(run)

    def test_missing_translator_is_a_setup_failure_not_a_proof_rejection(self):
        request = {**self.request, 'rust_tools': {'charon': '/nonexistent/flare-charon'}}
        save(self.root/'request.json', request)
        result = certify(self.root/'request.json', self.root/'missing-tool')
        self.assertEqual(result['status'], 'unresolved')
        self.assertEqual(result['failure_kind'], 'missing_tool')
        self.assertNotIn('lean_root_checked', result['completed_stages'])

    def test_translator_cannot_silently_include_unfrozen_source(self):
        (self.root/'src').mkdir()
        (self.root/'src/lib.rs').write_text('pub fn kernel() {}')
        record = {'has_errors': False, 'translated': {'crate_name': 'numerics_kernel',
            'files': [{'crate_name': 'numerics_kernel', 'name': {'Local': 'src/lib.rs'},
                       'contents': 'pub fn kernel() {}'}]}}
        self.assertEqual(check_extracted_files(record, self.root, ['src/lib.rs']), ['src/lib.rs'])
        outside = self.root/'outside.rs'
        outside.write_text('unfrozen include')
        record['translated']['files'].append({'crate_name': 'numerics_kernel',
            'name': {'Local': str(outside)}, 'contents': outside.read_text()})
        with self.assertRaisesRegex(ValueError, 'outside the frozen crate selection'):
            check_extracted_files(record, self.root, ['src/lib.rs'])
        record['translated']['files'].pop()
        record['translated']['files'][0]['contents'] = 'changed while extracting'
        with self.assertRaisesRegex(ValueError, 'differs from frozen contents'):
            check_extracted_files(record, self.root, ['src/lib.rs'])


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION') == '1' and
                     os.environ.get('FLARE_NUMERICS_RUST_TOOLS'),
                     'Set FLARE_NUMERICS_RUST_TOOLS for full Rust application checks')
class ApplicationLeanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        parent = ROOT/'.cache/numerics-generated'
        parent.mkdir(parents=True, exist_ok=True)
        cls.root = Path(tempfile.mkdtemp(prefix='application-tests-', dir=parent))
        cls.request = selected_request()
        cls.request['rust_tools'] = json.loads(
            Path(os.environ['FLARE_NUMERICS_RUST_TOOLS']).read_text())['rust_tools']
        save(cls.root/'request.json', cls.request)
        cls.baseline = cls.root/'baseline'
        result = certify(cls.root/'request.json', cls.baseline)
        if result['status'] != 'certified':
            raise AssertionError('Application baseline failed: '+json.dumps(result))

    def clone(self, name):
        destination = self.root/name
        shutil.copytree(self.baseline, destination)
        return destination

    def reseal(self, run, name):
        result = json.loads((run/'result.json').read_text())
        result['artifacts'][name] = sha(run/name)
        save(run/'result.json', result)

    def test_full_api_root_and_debug_release_edge_cases(self):
        result = json.loads((self.baseline/'result.json').read_text())
        self.assertEqual(result['entry_theorem'], 'Workflow.Certificate.certificate')
        self.assertIn('lean_root_checked', result['completed_stages'])
        self.assertEqual((self.baseline/'rust/src/imu_epoch.rs').read_bytes(),
                         (ROOT/'benchmarks/numerics/scale/imu48.rs').read_bytes())
        for mode in ('debug', 'release'):
            diagnostics = (self.baseline/'runs'/('rust-tests-'+mode)/'stdout.txt').read_text()
            self.assertIn('8 passed', diagnostics)
        check = (self.baseline/'runs/lean-Workflow-Check/stdout.txt').read_text()
        self.assertIn('transitive axioms checked', check)

    def test_saved_replay_needs_no_translator_rust_compiler_or_producer(self):
        frozen = self.clone('relocated')
        request = json.loads((frozen/'request.json').read_text())
        request['rust_tools'].update(charon='/absent/charon', aeneas='/absent/aeneas')
        save(frozen/'request.json', request)
        self.reseal(frozen, 'request.json')
        with patch('numerics.application.extract', side_effect=AssertionError('extractor called')), \
             patch('numerics.workflow.analyze', side_effect=AssertionError('producer called')):
            result = replay_run(frozen, self.root/'replay')
        self.assertEqual(result['status'], 'replayed')
        self.assertFalse(any(p.name.startswith(('rust-', 'extract', 'translate'))
                             for p in (self.root/'replay/runs').iterdir()))

    def test_weakened_root_is_rejected_even_after_artifact_reseal(self):
        frozen = self.clone('weak-root')
        name = 'lean/Workflow/Proof.lean'
        (frozen/name).write_text('''module
public import Workflow.Contract
@[expose] public section
namespace Workflow.Certificate
theorem certificate : True := trivial
end Workflow.Certificate
''')
        self.reseal(frozen, name)
        with self.assertRaisesRegex(RuntimeError, 'lean-Workflow-Check'):
            replay_run(frozen, self.root/'weak-replay')

    def test_additional_axiom_cannot_certify_the_correct_root_type(self):
        frozen = self.clone('axiom-root')
        name = 'lean/Workflow/Proof.lean'
        (frozen/name).write_text('''module
public import Workflow.Contract
public import Workflow.Generated.Funs
@[expose] public section
namespace Workflow.Certificate
axiom certificate : Workflow.Contract.Statement Workflow.Generated.imu_epoch.assess
end Workflow.Certificate
''')
        self.reseal(frozen, name)
        with self.assertRaisesRegex(RuntimeError, 'lean-Workflow-Check'):
            replay_run(frozen, self.root/'axiom-replay')
        diagnostic = (self.root/'axiom-replay/runs/lean-Workflow-Check/stdout.txt').read_text()
        self.assertIn('Unexpected axiom', diagnostic)

    def test_inadequate_padding_in_actual_source_and_model_fails_numerical_proof(self):
        request = copy.deepcopy(self.request)
        rust = self.root/'zero-padding.rs'
        rust.write_text(Path(request['source']).read_text().replace(
            'DECISION_PADDING: f64 = 3.725290298461914e-9', 'DECISION_PADDING: f64 = 0.0'))
        request['source'] = str(rust)
        request['rust_application']['files']['src/imu_epoch.rs'] = str(rust)
        module = 'Workflow.Subject.Implementation.IMUEpochApplication'
        model = self.root/'zero-padding.lean.txt'
        model.write_text(Path(request['rust_application']['lean_modules'][module]).read_text().replace(
            '0x3e30000000000000', '0x0000000000000000'))
        request['rust_application']['lean_modules'][module] = str(model)
        save(self.root/'zero-padding.json', request)
        result = certify(self.root/'zero-padding.json', self.root/'zero-padding')
        self.assertEqual(result['status'], 'unresolved')
        self.assertEqual(result['failure_kind'], 'stage_rejected')
        self.assertEqual(result['failure_stage'],
                         'lean-Workflow-Subject-Proofs-FloatIMUEpochApplication')
        # Fresh extraction and source correspondence passed first. The checked
        # numerical padding fact fails; tool absence cannot satisfy this test.
        self.assertIn('rust_extracted', result['completed_stages'])
        self.assertEqual(json.loads((self.root/'zero-padding/runs/lean-Workflow-Equivalence-IMUEpochApplication/run.json').read_text())['returncode'], 0)

    def test_changed_timestamp_path_cannot_reuse_the_original_bridge(self):
        request = copy.deepcopy(self.request)
        companion = self.root/'wrong-scale.rs'
        source = request['rust_application']['files']['src/timestamp_alignment.rs']
        companion.write_text(Path(source).read_text().replace('1.0e-9', '1.0e-8'))
        request['rust_application']['files']['src/timestamp_alignment.rs'] = str(companion)
        save(self.root/'wrong-scale.json', request)
        result = certify(self.root/'wrong-scale.json', self.root/'wrong-scale')
        self.assertEqual(result['status'], 'unresolved')
        self.assertEqual(result['failure_stage'], 'lean-Workflow-Equivalence-TimestampAlignment')
