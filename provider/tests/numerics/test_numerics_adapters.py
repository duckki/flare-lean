"""Source semantics and runtime admission for the common scalar adapters."""
from fractions import Fraction as Q
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from numerics.analysis.bounds import analyze
from numerics.frontends.scalar import FRONTENDS, Unsupported, execute, parse, word
from numerics.runtimes.source import command, julia_string, matlab_string, runtime_selection, validate_selection
from numerics.workflow.certification import audit_run, certify, prepare, save, sha


ROOT = Path(__file__).resolve().parents[3]


class CommonSourceTests(unittest.TestCase):
    def test_python_swap_updating_assignment_and_annotations_preserve_values(self):
        source = ('def f(x, y, /) -> tuple[float, float]:\n'
                  '    x, y = y, x\n    x += 1\n    y: float = +y\n    return x, y\n')
        program = parse('python', source, 'f')
        function = FRONTENDS['python'].load_for_diagnostics(source, 'f')
        for values in [(1e16, -1e16), (0.0, -0.0), (float.fromhex('0x0.0000000000001p-1022'), 0.5)]:
            self.assertEqual(tuple(map(word, execute(program, values))), tuple(map(word, function(*values))))

    def test_integer_promotions_preserve_signed_zero_and_never_admit_integer_computation(self):
        p = parse('python', 'def f(x):\n    c = -0\n    return c * x, -0.0 * x\n', 'f')
        self.assertEqual(tuple(map(word, execute(p, (1.0,)))), (0, 1 << 63))
        for expression in ['(1 + 2) * x', '(1 / 10) * x', '9007199254740993 + x', 'True + x', '1']:
            with self.subTest(expression=expression), self.assertRaises(Unsupported):
                parse('python', 'def f(x):\n    return '+expression+'\n', 'f')
        # An annotation alone must not coerce the local integer to a float.
        with self.assertRaises(Unsupported):
            parse('python', 'def f(x):\n    c: float = 1\n    return (c + 2) * x\n', 'f')

    def test_python_annotations_cannot_execute_arbitrary_code(self):
        for annotation in ['float()', 'list[float]', '__import__("os")', 'tuple[float, int]']:
            with self.subTest(annotation=annotation), self.assertRaises(Unsupported):
                parse('python', 'def f(x) -> '+annotation+':\n    return x\n', 'f')

    def test_julia_and_matlab_preserve_grouping_and_left_associative_division(self):
        sources = {
            'julia': 'function f(x::Float64, y, z)\n return x + y + z, x + (y + z)\nend\n',
            'matlab': 'function [a,b] = f(x,y,z)\na=x+y+z; b=x+(y+z);\nend\n'}
        for language, source in sources.items():
            with self.subTest(language=language):
                p = parse(language, source, 'f')
                self.assertEqual(execute(p, (1e16, -1e16, 1.0)), (1.0, 0.0))
        p = parse('julia', 'f(x, y, z) = x / y / z\n', 'f')
        self.assertEqual(execute(p, (12.0, 3.0, 2.0)), (2.0,))
        self.assertNotEqual(execute(p, (12.0, 3.0, 2.0)), (12.0/(3.0/2.0),))

    def test_julia_explicit_implicit_short_and_updating_functions(self):
        for source in ['function f(x::Float64)\n x += 1\nend\n',
                       'function f(x)\n y = x + 1\n y\nend\n',
                       'f(x::Float64) = x + 1\n']:
            with self.subTest(source=source):
                self.assertEqual(execute(parse('julia', source, 'f'), (2.0,)), (3.0,))

    def test_matlab_literals_are_double_and_scalar_dot_operators_are_admitted(self):
        source = 'function [a,b] = f(x)\n% double literals\na = (1 / 10) .* x;\nb = 1 ./ ...\n (2 + x);\nreturn;\nend\n'
        self.assertEqual(execute(parse('matlab', source, 'f'), (2.0,)), (0.2, 0.25))
        with self.assertRaisesRegex(Unsupported, 'Integer-only'):
            parse('julia', 'f(x) = (1 / 10) * x\n', 'f')
        # One MATLAB function may omit its final end; header outputs may use spaces.
        p = parse('matlab', 'function [a b]=f(x)\na=x+1; b=x-1;\n', 'f')
        self.assertEqual(execute(p, (2.0,)), (3.0, 1.0))

    def test_unmodelled_language_features_and_malformed_modules_are_rejected(self):
        julia = ['using LinearAlgebra\nf(x)=x+x', 'f(x::Float32)=x+x', 'f(x)=sin(x)',
                 'f(x)=x^2', 'f(x)=2x', 'f(x)=x .* x', '@fastmath f(x)=x+x',
                 'function f(x)\nreturn x\nx=x+x\nend', 'f(x)=x; run(`touch bad`)',
                 'function f(x)\n#= start\nreturn x\nend', 'f(x,x)=x+x']
        matlab = ['function y=f(x)\ny=[x,x];\nend', 'function y=f(x)\ny=x(1);\nend',
                  'function y=f(x)\ny=x\\x;\nend', 'function y=f(x)\ny=single(x);\nend',
                  'function y=f(x)\nif x>0\ny=x;\nend\nend', 'function y=f(x)\nend',
                  'function y=f(x)\nreturn;\ny=x;\nend', 'function y=f(x)\ny=x;\nend\nx=1;',
                  'function y=f(x)\ny=x;\n%{\nend', 'function [y,z]=f(x)\ny=x;\nend']
        for language, sources in [('julia', julia), ('matlab', matlab)]:
            for source in sources:
                with self.subTest(language=language, source=source), self.assertRaises((Unsupported, ValueError)):
                    parse(language, source, 'f')
        for source in ['', '# comment only', 'function f(x)\nreturn (x+x\nend']:
            with self.subTest(source=source), self.assertRaises(Unsupported):
                parse('julia', source, 'f')

    def test_examples_share_numerical_analysis_without_application_specific_dispatch(self):
        baseline = prepare(ROOT/'examples/numerics/scalar/scalar_kalman.json')
        expected, _ = analyze(baseline[2], baseline[0]['domain'])
        expected_bounds = [expected[x].e for x in baseline[2].outputs]
        for example in ['idiomatic_kalman', 'julia_kalman', 'matlab_kalman']:
            request, _, program, questions = prepare(ROOT/'examples/numerics/scalar'/f'{example}.json')
            self.assertFalse(questions)
            bounds, _ = analyze(program, request['domain'])
            self.assertEqual([bounds[x].e for x in program.outputs], expected_bounds)
            self.assertTrue(all(bounds[x].e < Q(t['limit']) for x, t in zip(program.outputs, request['outputs'], strict=True)))


class RuntimeAdmissionTests(unittest.TestCase):
    def test_runtime_executable_identity_is_part_of_current_freshness(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root/'original'; source.write_text('source')
            executable = root/'runtime'; executable.write_text('runtime version one')
            save(root/'source-runtime.json', {'executable': str(executable), 'executable_sha256': sha(executable)})
            save(root/'result.json', {'status': 'certified', 'source_path': str(source),
                'source_sha256': sha(source), 'artifacts': {'source-runtime.json': sha(root/'source-runtime.json')}})
            self.assertEqual(audit_run(root)['status'], 'fresh')
            executable.write_text('runtime version two')
            with self.assertRaisesRegex(ValueError, 'runtime executable changed'):
                audit_run(root)
            self.assertEqual(audit_run(root, frozen=True)['status'], 'fresh')

    def test_runtime_selection_is_explicit_and_never_substitutes_graph_execution(self):
        p = parse('matlab', 'function y=f(x)\ny=x+x;\nend', 'f')
        with patch('numerics.runtimes.source.shutil.which', return_value=None):
            with self.assertRaisesRegex(RuntimeError, 'Missing source runtime'):
                runtime_selection(p, {})
        for selection in [{'kind': 'julia'}, {'kind': 'octave', 'executable': ['octave']}, {'kind':'octave', 'args': ['--eval']}]:
            with self.subTest(selection=selection), self.assertRaises(ValueError):
                validate_selection(p, selection)
        runtime = {'kind': 'octave', 'executable': '/tmp/my octave'}
        self.assertEqual(command(runtime, '/tmp/source name.m')[-1], '/tmp/source name.m')
        self.assertIn('--no-init-file', command(runtime))
        self.assertEqual(julia_string('a$b'), '"a\\$b"')
        self.assertEqual(matlab_string("a'b"), "'a''b'")

    def test_missing_runtime_stops_before_bound_or_rust_generation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = ROOT/'examples/numerics/scalar/julia_kalman.json'
            request = json.loads(source.read_text())
            request['source'] = str((source.parent/request['source']).resolve())
            save(root/'request.json', request)
            with patch('numerics.runtimes.source.shutil.which', return_value=None), patch('numerics.workflow.certification.Runner.run', side_effect=AssertionError('must not run')):
                result = certify(root/'request.json', root/'out')
            self.assertEqual(result['status'], 'unresolved')
            self.assertIn('Missing source runtime', result['error'])
            self.assertNotIn('bounds_proposed', result['completed_stages'])
            self.assertFalse((root/'out/rust').exists())


if __name__ == '__main__':
    unittest.main()
