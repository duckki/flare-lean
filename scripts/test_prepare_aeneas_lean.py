"""Cold setup must restore model dependencies without mixing revisions or fetching all Mathlib."""
import json
from pathlib import Path
import tempfile
import unittest

from prepare_aeneas_lean import dependency_targets


class ModelDependencySetupTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.flare = Path(self.temp.name) / 'flare'
        self.aeneas = Path(self.temp.name) / 'aeneas'
        self.backend = self.aeneas / 'backends/lean'
        for root in [self.flare, self.backend]:
            root.mkdir(parents=True)
            (root / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
            (root / 'lake-manifest.json').write_text(json.dumps({'packages': [
                {'name': name, 'type': 'git', 'url': 'https://example.org/' + name, 'rev': name + '-revision'}
                for name in ['mathlib', 'batteries']]}))
        (self.backend / 'Aeneas.lean').write_text('import Aeneas.Model\n')
        (self.backend / 'AeneasMeta.lean').write_text('meta import AeneasMeta.Tools\n')
        (self.backend / 'Aeneas').mkdir()
        self.source = self.backend / 'Aeneas/Model.lean'
        self.source.write_text('''module
public import Mathlib.Data.List.GetD
meta import Mathlib.Control.Monad.Cont
private meta import all Batteries.Data.BitVec.Lemmas
import Lean Std
/- A documentation example must not fetch all Mathlib:
import Mathlib
-/
def example := "import Mathlib"
''')

    def test_restores_the_actual_cold_setup_gaps_including_meta_imports(self):
        self.assertEqual(dependency_targets(self.flare, self.aeneas), [
            'Batteries.Data.BitVec.Lemmas', 'Mathlib.Control.Monad.Cont', 'Mathlib.Data.List.GetD'])

    def test_rejects_incompatible_toolchain_or_shared_dependency(self):
        (self.backend / 'lean-toolchain').write_text('leanprover/lean4:v4.34.1\n')
        with self.assertRaisesRegex(ValueError, 'same Lean toolchain'):
            dependency_targets(self.flare, self.aeneas)
        (self.backend / 'lean-toolchain').write_text((self.flare / 'lean-toolchain').read_text())
        path = self.backend / 'lake-manifest.json'
        manifest = json.loads(path.read_text())
        manifest['packages'][1]['rev'] = 'another-batteries-revision'
        path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, 'Incompatible model dependency: batteries'):
            dependency_targets(self.flare, self.aeneas)

    def test_does_not_silently_turn_bootstrap_into_a_full_mathlib_build(self):
        self.source.write_text('import Mathlib\n')
        with self.assertRaisesRegex(ValueError, 'all of Mathlib'):
            dependency_targets(self.flare, self.aeneas)


if __name__ == '__main__':
    unittest.main()
