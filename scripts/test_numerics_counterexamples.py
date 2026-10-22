"""A real numerical failure, with a kernel-checked witness rather than a loose bound."""
from fractions import Fraction as Q
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from numerics.counterexample import certificate_source
from numerics.frontend import execute, parse


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'examples/numerics/naive_covariance.py'


class CounterexampleDiagnosticsTests(unittest.TestCase):
    def test_actual_python_and_its_ordered_model_lose_strict_positivity(self):
        source = SOURCE.read_text()
        namespace = {}
        exec(compile(source, str(SOURCE), 'exec'), namespace)
        p, r = 1.0, 2.0 ** -54
        native = namespace['posterior_variance'](p, r)
        program = parse('python', source, 'posterior_variance')
        self.assertEqual(execute(program, (p, r)), (native,))
        self.assertEqual(native, 0.0)
        exact = Q.from_float(p) * Q.from_float(r) / (Q.from_float(p) + Q.from_float(r))
        self.assertEqual(exact, Q(1, 2**54 + 1))
        self.assertGreater(exact, 0)


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION') == '1',
                     'Run make numerics-check for the kernel-checked counterexample')
class CounterexampleLeanTests(unittest.TestCase):
    def test_failure_certificate_replays_and_a_false_outcome_is_rejected(self):
        with tempfile.TemporaryDirectory(prefix='flare-counterexample-') as directory:
            root = Path(directory)
            source = certificate_source(SOURCE.read_text())
            for name in ['certificate', 'replay']:
                path = root / (name + '.lean')
                path.write_text(source)
                result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                    text=True, capture_output=True, timeout=120)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn('Checked NaiveCovarianceFailure.failure', result.stdout)
            wrong = root / 'wrong.lean'
            wrong.write_text(source + '''
theorem false_outcome : Workflow.kernel 1.0 NaiveCovarianceFailure.noise = 1.0 := by
  decide +kernel
''')
            result = subprocess.run(['lake', 'env', 'lean', str(wrong)], cwd=ROOT,
                text=True, capture_output=True, timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Tactic `decide` proved that the proposition', result.stdout)
            self.assertIn('is false', result.stdout)


if __name__ == '__main__':
    unittest.main()
