"""Shared adapter extension, semantic binding and real optional producer checks."""
from dataclasses import replace
from fractions import Fraction as Q
import json
import os
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest.mock import patch

from numerics.adapter_external import parse_fptaylor
from numerics.frontend import Unsupported, parse
from numerics.emit import proof_source
from numerics.installation import setup, unpack
from numerics.integration import Adapter, Session, ToolError, adapters, replay_evidence, validate
from numerics.workflow import Runner, certify, output_bounds, prepare, replay_run, save, sha


SOURCE = 'def f(x, y):\n    return x + y\n'
REQUEST = {'schema': 'numerics-request-v1', 'source': 'source.py', 'function': 'f',
           'language': 'python', 'domain': {'x': ['-1', '1'], 'y': ['-1', '1']},
           'specification': ['x+y'],
           'outputs': [{'name': 'sum', 'unit': 'm', 'limit': '1/1000000'}]}


class IntegrationTests(unittest.TestCase):
    def test_semantic_mismatch_and_unsupported_adapter_fail_before_execution(self):
        program = parse('python', SOURCE, 'f')
        with self.assertRaisesRegex(Unsupported, 'arithmetic model'):
            validate({**REQUEST, 'arithmetic': {'format': 'binary32'}}, program)
        with self.assertRaisesRegex(Unsupported, 'producer adapter'):
            validate({**REQUEST, 'producer': 'missing'}, program)
        with self.assertRaisesRegex(Unsupported, 'dyadic'):
            validate({**REQUEST, 'producer': 'gappa', 'domain': {'x': ['0', '1/10']}}, program)

    def test_candidates_are_read_exactly_and_malformed_output_is_rejected(self):
        # The decimal is deliberately less precise than the retained hex upper value.
        self.assertEqual(parse_fptaylor('Absolute error (exact): 3.3e-16 (0x1.8p-52)'),
                         str(Q(3, 2**53)))
        for text in ['absolute error = 0', 'Absolute error (exact): nan',
                     'Absolute error (exact): 1 (0x1p+999999999)',
                     'Absolute error (exact): 0 (0x0p+0)\nAbsolute error (exact): 0 (0x0p+0)']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                parse_fptaylor(text)

    def test_tool_setup_identity_and_version_failures_are_distinct(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'source.py').write_text(SOURCE)
            program = parse('python', SOURCE, 'f')
            tool = root/'tool'
            tool.write_text('#!'+sys.executable+'\nprint("Gappa 0.0")\n')
            tool.chmod(0o755)
            request = {**REQUEST, 'analysis_tools': {'gappa': {'executable': str(tool)}}}
            session = Session(program, request, root, root, Runner(root), output_bounds, 'source.py')
            with self.assertRaises(ToolError) as error:
                session.tool('gappa', ['--version'], r'Gappa (\S+)', ['1.8.3'])
            self.assertEqual(error.exception.kind, 'unsupported_tool_version')
            request['analysis_tools']['gappa']['sha256'] = '0'*64
            with self.assertRaises(ToolError) as error:
                session.tool('gappa', ['--version'], r'Gappa (\S+)', ['1.8.3'])
            self.assertEqual(error.exception.kind, 'tool_identity_mismatch')
            request['analysis_tools']['gappa'] = {'executable': str(root/'absent')}
            with self.assertRaises(ToolError) as error:
                session.tool('gappa', ['--version'], r'Gappa (\S+)', ['1.8.3'])
            self.assertEqual(error.exception.kind, 'missing_tool')

    def test_archive_setup_rejects_paths_outside_the_installation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            archive = root/'source.tar.gz'
            with tarfile.open(archive, 'w:gz') as stream:
                stream.addfile(tarfile.TarInfo('../outside'))
            with self.assertRaisesRegex(ValueError, 'archive member'):
                unpack(archive, root/'unpacked')
            self.assertFalse((root/'outside').exists())

    def test_new_source_recipe_uses_shared_setup_and_preserves_existing_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repository = root/'vendor'; repository.mkdir()
            def git(*args):
                return subprocess.check_output(['git', *args], cwd=repository, text=True, stderr=subprocess.STDOUT).strip()
            git('init', '-q')
            (repository/'README').write_text('Local tool fixture\n')
            git('add', 'README')
            git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid', 'commit', '-qm', 'tool')
            revision = git('rev-parse', 'HEAD')
            adapter = Adapter('fixture', 'producer', 'candidate', 'test fixture', None, setup={
                'source': {'repository': str(repository), 'revision': revision},
                'commands': [[sys.executable, '-c', "from pathlib import Path; p=Path('tool'); p.write_text('#!/bin/sh\\necho fixture\\n'); p.chmod(0o755)"]],
                'executable': 'source/tool'})
            with patch('numerics.installation.adapters', return_value={'fixture': adapter}):
                record = setup('fixture', root/'installed', timeout=30)
                self.assertEqual(record['status'], 'installed')
                self.assertEqual(record['sha256'], sha(root/'installed/source/tool'))
                with self.assertRaises(FileExistsError):
                    setup('fixture', root/'installed')


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION') == '1', 'Run make numerics-check')
class AdapterLeanTests(unittest.TestCase):
    def test_adapter_generated_lean_module_uses_the_same_root_and_replay(self):
        def imported(session):
            summaries, steps = session.baseline(session.program, session.request)
            module = proof_source(session.program, session.request['domain'], summaries, steps,
                                  session.request['outputs'])
            module = module.split('\ntheorem specification_equiv', 1)[0]
            module = module.replace('namespace Workflow.Certificate', 'namespace Workflow.AdapterProof')
            module += '\nend Workflow.AdapterProof\n'
            from numerics.integration import Proposal
            value = Proposal(summaries, steps, {name: summaries[name] for name in session.program.outputs},
                {'validation': 'adapter-lean-module'}, lean_source=module,
                authored={'accuracy': 'Workflow.AdapterProof.accuracy'})
            return value, value.details
        adapter = Adapter('lean-module', 'producer', 'lean-source', 'Generated module fixture', imported)
        with tempfile.TemporaryDirectory() as directory, patch('numerics.integration.adapters',
                return_value={**adapters(), adapter.name: adapter}):
            root = Path(directory); (root/'source.py').write_text(SOURCE)
            save(root/'request.json', {**REQUEST, 'producer': adapter.name})
            result = certify(root/'request.json', root/'certificate')
            self.assertEqual(result['status'], 'certified', result)
            self.assertTrue((root/'certificate/validation.json').exists())
            with patch.object(Session, 'execute', side_effect=AssertionError('adapter called')), \
                 patch('numerics.integration.adapters', side_effect=AssertionError('registry called')):
                self.assertEqual(replay_run(root/'certificate', root/'replay')['status'], 'replayed')

    def test_additional_adapter_reuses_workflow_and_false_claim_is_rejected(self):
        def proposal(session):
            value = session.budget_proposal({'evidence_form': 'test-candidates'})
            return value, value.details
        adapter = Adapter('additional', 'producer', 'numeric-candidates', 'Extension fixture', proposal)
        registry = {**adapters(), adapter.name: adapter}
        with tempfile.TemporaryDirectory() as directory, patch('numerics.integration.adapters', return_value=registry):
            root = Path(directory); (root/'source.py').write_text(SOURCE)
            save(root/'request.json', {**REQUEST, 'producer': adapter.name})
            run = root/'valid'
            result = certify(root/'request.json', run)
            self.assertEqual(result['status'], 'certified', result)
            with patch.object(Session, 'execute', side_effect=AssertionError('producer called')), \
                 patch('numerics.integration.adapters', side_effect=AssertionError('registry called')):
                self.assertEqual(replay_run(run, root/'replay')['status'], 'replayed')
            # A producer may lie; its selected numerical claim must still fail in Lean.
            def false_proposal(session):
                value, details = proposal(session)
                value.claims = {name: replace(bound, e=Q(0)) for name, bound in value.claims.items()}
                return value, details
            registry[adapter.name] = replace(adapter, execute=false_proposal)
            result = certify(root/'request.json', root/'false')
            self.assertEqual((result['status'], result['failure_stage']), ('unresolved', 'lean-proof'))
            self.assertNotIn('lean_root_checked', result['completed_stages'])
            # Even a rehashed metadata change cannot attach evidence to another obligation.
            frozen = json.loads((run/'obligation.json').read_text())
            frozen['domain']['x'] = ['-2', '2']; save(run/'obligation.json', frozen)
            request, _, program, _ = prepare(run/'request.json')
            with self.assertRaisesRegex(ValueError, 'does not match'):
                replay_evidence(run, request, program)


@unittest.skipUnless(os.environ.get('FLARE_NUMERICS_INTEGRATION') == '1' and
                     os.environ.get('FLARE_NUMERICS_ANALYSIS_TOOLS'),
                     'Set FLARE_NUMERICS_ANALYSIS_TOOLS for real external producer checks')
class ExternalProducerTests(unittest.TestCase):
    def test_foreign_success_cannot_replace_an_independent_lean_proof(self):
        configuration = json.loads(Path(os.environ['FLARE_NUMERICS_ANALYSIS_TOOLS']).read_text())
        tools = configuration.get('analysis_tools', configuration)
        with tempfile.TemporaryDirectory(prefix='flare-external-rejection-') as directory:
            root = Path(directory); (root/'source.py').write_text(SOURCE)
            for producer in ['gappa', 'fptaylor']:
                with self.subTest(producer=producer):
                    request = {**REQUEST, 'producer': producer, 'analysis_tools': tools,
                               'outputs': [{'name': 'sum', 'unit': 'm', 'limit': str(Q(2)**-50)}]}
                    save(root/'request.json', request)
                    run = root/producer
                    result = certify(root/'request.json', run)
                    self.assertEqual((result['status'], result['failure_stage']), ('unresolved', 'lean-proof'))
                    command = json.loads((run/'runs'/(producer+'-output-0')/'run.json').read_text())
                    self.assertEqual(command['returncode'], 0, command)
                    self.assertNotIn('lean_root_checked', result['completed_stages'])
                    self.assertNotIn('accepted_bounds', json.loads((run/'analysis.json').read_text()))

    def test_real_tools_check_a_family_and_replay_without_producers(self):
        configuration = json.loads(Path(os.environ['FLARE_NUMERICS_ANALYSIS_TOOLS']).read_text())
        tools = configuration.get('analysis_tools', configuration)
        cases = [
            (SOURCE, REQUEST['domain'], ['x+y']),
            ('def f(x, y):\n    return x*y+x\n', {'x': ['-2', '2'], 'y': ['0', '1']}, ['x*y+x']),
            ('def f(x, y):\n    return x / (y + 2.0)\n', {'x': ['-1', '1'], 'y': ['1', '2']}, ['x/(y+2)']),
        ]
        with tempfile.TemporaryDirectory(prefix='flare-external-tools-') as directory:
            root = Path(directory)
            for producer in ['gappa', 'fptaylor']:
                for index, (source, domain, specification) in enumerate(cases):
                    with self.subTest(producer=producer, case=index):
                        (root/'source.py').write_text(source)
                        request = {**REQUEST, 'producer': producer, 'domain': domain,
                                   'specification': specification, 'analysis_tools': tools}
                        save(root/'request.json', request)
                        run = root/(producer+'-'+str(index))
                        result = certify(root/'request.json', run)
                        self.assertEqual(result['status'], 'certified', result)
                        evidence = json.loads((run/'evidence.json').read_text())
                        self.assertEqual(evidence['records'][0]['name'], producer)
                        self.assertTrue(evidence['tools'])
                        with patch.object(Session, 'tool', side_effect=AssertionError('tool admission called')), \
                             patch.object(Session, 'execute', side_effect=AssertionError('producer called')):
                            replayed = replay_run(run, root/(producer+'-'+str(index)+'-replay'))
                        self.assertEqual(replayed['status'], 'replayed')


if __name__ == '__main__':
    unittest.main()
