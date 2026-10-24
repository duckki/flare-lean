"""Regressions for source semantics, adapter admission, requests and stale evidence."""
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from numerics.analysis.bounds import analyze
from numerics.frontends.scalar import FRONTENDS, SourceAdapter, Unsupported, execute, parse, python_frontend, word
from numerics.workflow.certification import audit_run, certify, prepare, save, sha
from numerics.emit.specification import lean_expression


class FrontendTests(unittest.TestCase):
    def test_source_order_is_preserved_under_cancellation(self):
        source = 'def f(x: float, y: float, z: float):\n    x = x + y\n    return x + z, y + z\n'
        program = parse('python', source, 'f')
        result = execute(program, (1e16, -1e16, 1.0))
        self.assertEqual(result, (1.0, -1e16))
        self.assertNotEqual(result[0], 1e16+(-1e16+1.0))

    def test_literals_and_zero_sign_are_retained(self):
        program = parse('python', 'def f(x: float):\n    return -0.0, 0.1 + x\n', 'f')
        result = execute(program, (0.0,))
        self.assertEqual(word(result[0]), 1 << 63)
        self.assertEqual(word(result[1]), word(0.1))

    def test_effects_branches_libraries_and_integer_arithmetic_are_not_silently_translated(self):
        sources = ['import numpy\ndef f(x: float):\n    return x\n',
            'def f(x: float):\n    return abs(x)\n',
            'def f(x: float):\n    if x > 0.0:\n        return x\n    return -x\n',
            'def f(x: float):\n    return x + (1 + 2)\n',
            'def f(x: int):\n    return x + x\n']
        for source in sources:
            with self.subTest(source=source), self.assertRaises(Unsupported):
                parse('python', source, 'f')

    def test_language_extension_reuses_the_graph_without_changing_analysis(self):
        def adapter(source, function):
            return replace(python_frontend(source, function), language='test-adapter')
        test_adapter = SourceAdapter(adapter, FRONTENDS['python'].load_for_diagnostics, 'Test-only adapter')
        with patch.dict(FRONTENDS, {'test-adapter': test_adapter}):
            program = parse('test-adapter', 'def f(x: float):\n    return x + x\n', 'f')
            bounds, _ = analyze(program, {'x': ['-1', '1']})
            self.assertGreater(bounds[program.outputs[0]].e, 0)
            self.assertEqual(program.language, 'test-adapter')
        with self.assertRaises(Unsupported):
            parse('not-a-language', 'anything', 'f')

    def test_division_requires_native_and_original_reference_denominators(self):
        program = parse('python', 'def f(x: float, y: float):\n    return x / y\n', 'f')
        with self.assertRaisesRegex(ValueError, 'denominator'):
            analyze(program, {'x': ['1', '2'], 'y': ['-1', '1']})

    def test_exact_specification_does_not_silently_round_decimal_constants(self):
        self.assertEqual(lean_expression('0.1 + x', ('x',)), '(((1 : ℝ) / 10) + a0)')
        for expression in ['abs(x)', 'unknown + x', 'x ** 2']:
            with self.subTest(expression=expression), self.assertRaises(ValueError):
                lean_expression(expression, ('x',))


class RequestAndEvidenceTests(unittest.TestCase):
    def test_missing_engineering_information_is_requested_before_running_tools(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'source.py').write_text('def f(x: float):\n    return x + x\n')
            save(root/'request.json', {'schema': 'numerics-request-v1', 'language': 'python',
                'source': 'source.py', 'function': 'f'})
            with patch('numerics.workflow.certification.Runner.run', side_effect=AssertionError('must not run')):
                result = certify(root/'request.json', root/'out')
            self.assertEqual(result['status'], 'needs_input')
            self.assertEqual({x['field'] for x in result['questions']}, {'domain.x', 'outputs', 'specification'})
            self.assertFalse((root/'out').exists())

    def test_freshness_rejects_changed_source_and_changed_rust_artifact(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root/'original.py'; source.write_text('original')
            artifact = root/'kernel.rs'; artifact.write_text('checked source')
            save(root/'result.json', {'status': 'certified', 'source_path': str(source),
                'source_sha256': sha(source), 'artifacts': {'kernel.rs': sha(artifact)}})
            self.assertEqual(audit_run(root)['status'], 'fresh')
            source.write_text('changed')
            with self.assertRaisesRegex(ValueError, 'Original source changed'):
                audit_run(root)
            self.assertEqual(audit_run(root, frozen=True)['status'], 'fresh')
            artifact.write_text('different Rust')
            with self.assertRaisesRegex(ValueError, 'artifact'):
                audit_run(root, frozen=True)

    def test_example_is_a_real_gain_computation_with_original_input_error(self):
        request = Path(__file__).resolve().parents[3]/'examples/numerics/scalar/scalar_kalman.json'
        r, _, program, questions = prepare(request)
        self.assertFalse(questions)
        self.assertIn('div', {n.op for n in program.nodes})
        bounds, _ = analyze(program, r['domain'])
        self.assertTrue(all(0 < bounds[n].e < Q(t['limit']) for n, t in zip(program.outputs, r['outputs'], strict=True)))


if __name__ == '__main__':
    unittest.main()
