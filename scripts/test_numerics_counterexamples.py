"""A real numerical failure, with a kernel-checked witness rather than a loose bound."""
from fractions import Fraction as Q
from pathlib import Path
import unittest

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


if __name__ == '__main__':
    unittest.main()
