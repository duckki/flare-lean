"""Combined applications: complete scalar API, dependency reuse and replay identity."""
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from numerics.workflow.application import check_source
from numerics.graph import Unsupported
from numerics.workflow.proof_cache import ApplicationCache
from numerics.integrations.rust import imported_model, matching_model
from numerics.frontends.source_api import lower
from numerics.workflow.certification import ROOT, audit_run, prepare, save, seal

FIXTURE = ROOT/'examples/numerics/planar'


def selected_request():
    request = json.loads((FIXTURE/'request.json').read_text())
    request['source'] = str(FIXTURE/request['source'])
    for field in ('files', 'lean_modules', 'components', 'licenses'):
        request['rust_application'][field] = {
            n: str(FIXTURE/p) for n, p in request['rust_application'][field].items()}
    return request


class CombinedAdmissionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='flare-components-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.source = (FIXTURE/'source/gh_filter.py').read_text()
        self.typ = 'Workflow.Generated.gh.GhFilter'

    def test_constructor_every_field_options_and_division_domain_are_lowered(self):
        text, record = lower(self.source, 'GHFilter.update', self.typ)
        self.assertEqual(record['fields'], ['x', 'dx', 'dt', 'g', 'h',
            'dx_prediction', 'x_prediction', 'y', 'z'])
        self.assertEqual(record['options'], {'g': 'g', 'h': 'h'})
        self.assertIn('g.getD s.g', text)
        self.assertIn('h.getD s.h', text)
        self.assertIn('s.dt.isFinite = true', text)
        self.assertIn('s.dt == (0.0 : Float)', text)
        self.assertIn('z := s.z', text)
        changed = self.source.replace('self.z = 0.', 'self.z = 1.')
        self.assertNotEqual(lower(changed, 'GHFilter.update', self.typ)[0], text)

    def test_unsupported_constructor_and_shadowed_numpy_are_rejected(self):
        variants = [self.source.replace('self.z = 0.', 'self.z = x + 1'),
            self.source.replace('self.z = 0.', 'self.z = -(x + 1)'),
            self.source.replace('self.dt = dt', 'np = x\n        self.dt = dt'),
            self.source.replace('self.z = 0.', 'self.z = custom(x)')]
        for source in variants:
            with self.subTest(source=source[-30:]), self.assertRaises(Unsupported):
                lower(source, 'GHFilter.update', self.typ)

    def test_composed_request_and_reserved_imports(self):
        request = selected_request()
        path = self.root/'request.json'
        save(path, request)
        _, _, program, questions = prepare(path)
        self.assertFalse(questions)
        self.assertEqual(list(program.components), ['Axis'])
        for module in ('Workflow.SourceAPI', 'Workflow.Components.Axis.Proof'):
            bad = copy.deepcopy(request)
            bad['rust_application']['lean_modules'][module] = __file__
            save(path, bad)
            with self.assertRaisesRegex(ValueError, 'reserved'):
                prepare(path)
        for selection in ({'axis': 'axis.json'}, {'Axis': str(FIXTURE/'request.json')}):
            bad = copy.deepcopy(request)
            bad['rust_application']['components'] = selection
            save(path, bad)
            with self.assertRaises(ValueError):
                prepare(path)

    def test_missing_python_diagnostic_tool_is_not_a_proof_rejection(self):
        from numerics.runtimes.api import run
        from numerics.integrations.registry import ToolError
        with self.assertRaises(ToolError) as rejected:
            run(self.root, {'rust_application': {'source_api': {'runtime': '/nonexistent/api-python'}}},
                None, self.root/'work')
        self.assertEqual(rejected.exception.kind, 'missing_tool')

    def test_independent_root_requires_source_api_conjunction(self):
        text = check_source('tracker::assess', source_api=True)
        self.assertIn('(Workflow.Contract.Statement Workflow.Generated.tracker.assess) ∧ Workflow.SourceAPI.Contract', text)
        self.assertIn('collectAxioms ``Workflow.Certificate.certificate', text)

    def test_nested_component_results_are_sealed(self):
        run = self.root/'run'
        (run/'components/Axis').mkdir(parents=True)
        save(run/'components/Axis/result.json', {'status': 'certified'})
        seal(run, {'status': 'certified'})
        self.assertEqual(audit_run(run, frozen=True)['status'], 'fresh')
        save(run/'components/Axis/result.json', {'status': 'unresolved'})
        with self.assertRaisesRegex(ValueError, 'Changed or missing artifact'):
            audit_run(run, frozen=True)

    def test_transitive_cache_keys_invalidate_affected_modules(self):
        lean = self.root/'lean'
        (lean/'Workflow').mkdir(parents=True)
        a, b, c = [lean/('Workflow/'+n+'.lean') for n in ('A', 'B', 'C')]
        a.write_text('module\npublic import Workflow.B\n')
        b.write_text('module\nimport Workflow.C\n')
        c.write_text('module\ndef localValue := 1\n')
        cache = ApplicationCache(self.root/'cache', {'model': 'one'}, lean)
        before = cache.entry(a)[0]
        c.write_text('module\ndef localValue := 2\n')
        self.assertNotEqual(cache.entry(a)[0], before)
        independent = cache.entry(c)[0]
        b.write_text('module\nimport Workflow.C\n-- changed contract\n')
        self.assertEqual(cache.entry(c)[0], independent)
        self.assertNotEqual(ApplicationCache(None, {'model':'two'}, lean).entry(c)[0], independent)
        c.write_text('module\nimport Workflow.A\n')
        with self.assertRaisesRegex(ValueError, 'Cyclic'):
            cache.entry(a)

    def test_imported_model_manifest_ignores_unused_files_but_detects_changes(self):
        for name in ('Aeneas', 'Helper'):
            for suffix in ('', '.private', '.server'):
                (self.root/(name+'.olean'+suffix)).write_text(name+suffix)
        record = imported_model(self.root, ['Aeneas', 'Helper', 'Mathlib.Unused'])
        self.assertTrue(matching_model(self.root, record))
        (self.root/'Unused.olean').write_text('unrelated build')
        self.assertTrue(matching_model(self.root, record))
        (self.root/'Helper.olean.private').write_text('changed proof model')
        self.assertFalse(matching_model(self.root, record))


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION') == '1' and
                     os.environ.get('FLARE_NUMERICS_RUST_TOOLS'), 'Requires optional Rust proof tools')
class CombinedLeanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        from numerics.workflow.certification import certify
        cls.root = Path(tempfile.mkdtemp(prefix='planar-tests-', dir=ROOT/'.cache/numerics-generated'))
        cls.request = selected_request()
        cls.request['rust_tools'] = json.loads(Path(os.environ['FLARE_NUMERICS_RUST_TOOLS']).read_text())['rust_tools']
        cls.request['contract_cache'] = str(cls.root/'contracts')
        save(cls.root/'request.json', cls.request)
        cls.result = certify(cls.root/'request.json', cls.root/'run')
        if cls.result['status'] != 'certified':
            raise AssertionError(cls.result)

    def test_single_root_and_frozen_replay_without_producers(self):
        from numerics.workflow.certification import replay_run
        self.assertEqual(self.result['entry_theorem'], 'Workflow.Certificate.certificate')
        with patch('numerics.workflow.application.extract', side_effect=AssertionError('translator called')), \
             patch('numerics.workflow.components.generate', side_effect=AssertionError('producer called')):
            replay = replay_run(self.root/'run', self.root/'replay')
        self.assertEqual(replay['status'], 'replayed')

    def test_frozen_component_and_api_models_are_regenerated(self):
        from numerics.workflow.certification import replay_run
        for name, relative in [('component', 'Workflow/Components/Axis/Kernel.lean'),
                               ('api', 'Workflow/SourceAPI.lean')]:
            clone = self.root/('tampered-'+name)
            import shutil
            shutil.copytree(self.root/'run', clone)
            target = clone/'lean'/relative
            target.write_text(target.read_text()+'\n-- changed after sealing\n')
            seal(clone, json.loads((clone/'result.json').read_text()))
            with self.assertRaisesRegex(ValueError, 'Imported component source changed|API model differs'):
                replay_run(clone, self.root/('tampered-'+name+'-replay'))

    def test_constructor_mutation_fails_full_state_bridge(self):
        from numerics.workflow.certification import certify
        request = copy.deepcopy(self.request)
        source = self.root/'changed-gh.rs'
        text = Path(request['rust_application']['files']['src/gh.rs']).read_text()
        self.assertIn('z: 0.0', text)
        source.write_text(text.replace('z: 0.0', 'z: 1.0'))
        request['rust_application']['files']['src/gh.rs'] = str(source)
        save(self.root/'changed.json', request)
        result = certify(self.root/'changed.json', self.root/'changed')
        self.assertEqual(result['status'], 'unresolved')
        self.assertEqual(result['failure_stage'], 'lean-Workflow-Bridge')
        self.assertNotIn('lean_root_checked', result['completed_stages'])

    def test_changed_padding_rechecks_application_and_reuses_axis_proofs(self):
        from numerics.workflow.certification import certify
        request = copy.deepcopy(self.request)
        changes = {
            'rust': ('DECISION_PADDING: f64 = 3.725290298461914e-9',
                     'DECISION_PADDING: f64 = 7.450580596923828e-9'),
            'Workflow.Native': ('0x3e30000000000000', '0x3e40000000000000'),
            'Workflow.Decisions': ('(-28 : Int)', '(-27 : Int)'),
            'Workflow.Contract': ('(-28 : Int)', '(-27 : Int)')}
        for name, (old, new) in changes.items():
            mapping = request['rust_application']['files' if name == 'rust' else 'lean_modules']
            key = 'src/tracker.rs' if name == 'rust' else name
            text = Path(mapping[key]).read_text()
            self.assertIn(old, text)
            if name == 'Workflow.Decisions':
                text = text.replace('(-80 : Int)', '(-79 : Int)')
            changed = self.root/(name.replace('.', '-')+('.rs' if name == 'rust' else '.lean.txt'))
            changed.write_text(text.replace(old, new))
            mapping[key] = str(changed)
            if name == 'rust':
                request['source'] = str(changed)
        request['contract_summary']['properties'][-1] = 'Strict decisions with widened padding; Uncertain radius 2^-27 + 2^-29.'
        save(self.root/'maintenance.json', request)
        result = certify(self.root/'maintenance.json', self.root/'maintenance')
        self.assertEqual(result['status'], 'certified', result.get('error'))
        reuse = json.loads((self.root/'maintenance/proof-reuse.json').read_text())['modules']
        axis = [r for r in reuse if '/Components/Axis/' in r['module']]
        self.assertTrue(axis and all(r['reused'] for r in axis))
        changed = [r for r in reuse if r['module'] == 'Workflow/Decisions.lean']
        self.assertTrue(changed and not changed[0]['reused'])

    @unittest.skipUnless(os.environ.get('FLARE_NUMERICS_RUST_UPGRADE'), 'Set an installed compatible Rust release')
    def test_compatible_runtime_upgrade_retains_proof_and_rechecks_runtime(self):
        from numerics.workflow.certification import certify
        request = copy.deepcopy(self.request)
        request['rust_runtime'] = os.environ['FLARE_NUMERICS_RUST_UPGRADE']
        save(self.root/'upgrade.json', request)
        result = certify(self.root/'upgrade.json', self.root/'upgrade')
        self.assertEqual(result['status'], 'certified', result.get('error'))
        self.assertIn('runtime_diagnostics', result['completed_stages'])
        self.assertIn(request['rust_runtime'], (self.root/'upgrade/runs/rust-version/stdout.txt').read_text())
