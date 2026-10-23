"""Reviewed Lean contracts for freshly extracted, multi-module Rust applications.

This is a proof-bundle interface, not an automatic Rust-to-specification frontend.
The contract is an explicit reviewed input, independent of the proof module.
"""
from dataclasses import dataclass, field
import json
import math
from pathlib import Path, PurePosixPath
import re
import shutil
import time

from .integration import ARITHMETIC, ToolError
from .rust import model_files, imported_model, matching_model, tools


@dataclass(frozen=True)
class Application:
    function: str
    files: dict
    modules: dict
    components: dict = field(default_factory=dict)
    language: str = 'rust'

    def record(self):
        return {'profile': 'rust-application-proof-v1', 'language': self.language,
                'entry': self.function, 'crate_files': list(self.files),
                'lean_modules': list(self.modules), 'components': list(self.components)}


def prepare(path, request, *, replay=False):
    """Admit a dependency-free Rust crate and explicitly authored contract/proofs."""
    base = Path(path).resolve().parent
    if request.get('language') != 'rust' or request.get('target') != 'rust-aeneas':
        raise ValueError('rust_application requires Rust and target rust-aeneas')
    incompatible = {'domain', 'outputs', 'specification', 'proof', 'rust_port',
                    'python_method', 'python_arrays', 'python_branches', 'analysis_tools',
                    'source_runtime'}
    if incompatible.intersection(request):
        raise ValueError('rust_application uses a reviewed Lean contract, not scalar/array fields')
    if request.get('backend', 'lean-flare') != 'lean-flare' or 'producer' in request:
        raise ValueError('rust_application checks an authored proof bundle in Lean')
    arithmetic = request.get('arithmetic', ARITHMETIC)
    if (arithmetic != ARITHMETIC or
            any(type(arithmetic[k]) is not type(v) for k, v in ARITHMETIC.items())):
        raise ValueError('Unsupported application arithmetic model')
    bundle = request['rust_application']
    required = {'entry', 'files', 'lean_modules'}
    if not isinstance(bundle, dict) or not required <= set(bundle) or set(bundle)-required-{'components', 'source_api', 'licenses'}:
        raise ValueError('rust_application needs entry, files and lean_modules')
    entry = bundle['entry']
    if (not isinstance(entry, str) or
            not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:::[A-Za-z_][A-Za-z_0-9]*)*', entry) or
            entry.split('::')[-1] != request['function']):
        raise ValueError('Application entry must end with the selected function')
    files, modules = bundle['files'], bundle['lean_modules']
    if not isinstance(files, dict) or 'src/lib.rs' not in files:
        raise ValueError('Application files must include src/lib.rs')
    for destination, source in files.items():
        if (not isinstance(destination, str) or not destination.startswith('src/') or
                PurePosixPath(destination).suffix != '.rs' or
                any(x in ('', '.', '..') for x in destination.split('/'))):
            raise ValueError('Application file must be a relative src/*.rs path')
        if not isinstance(source, str) or not (base/source).is_file():
            raise ValueError('Missing Rust application source: '+str(source))
    licenses = bundle.get('licenses', {})
    if (not isinstance(licenses, dict) or any(not isinstance(n, str) or
            not re.fullmatch(r'LICENSE[A-Za-z0-9_.-]*', n) or not isinstance(p, str) or
            not (base/p).is_file() for n, p in licenses.items())):
        raise ValueError('licenses must map LICENSE names to existing attribution files')
    selected = (base/request['source']).resolve()
    if selected not in [(base/p).resolve() for p in files.values()]:
        raise ValueError('Selected source must be one of the frozen crate files')
    if not isinstance(modules, dict) or not {'Workflow.Contract', 'Workflow.Proof'} <= modules.keys():
        raise ValueError('Bundle needs separate Workflow.Contract and Workflow.Proof modules')
    for module, source in modules.items():
        if (not isinstance(module, str) or
                not re.fullmatch(r'Workflow(?:\.[A-Za-z_][A-Za-z_0-9]*)+', module) or
                module.startswith(('Workflow.Generated.', 'Workflow.Components.')) or
                module in ('Workflow.Generated', 'Workflow.Check', 'Workflow.SourceAPI')):
            raise ValueError('Invalid or reserved application Lean module: '+str(module))
        if not isinstance(source, str) or not (base/source).is_file():
            raise ValueError('Missing application Lean module: '+str(source))
    timeout = request.get('timeout_seconds', 240)
    if type(timeout) not in (int, float) or not math.isfinite(timeout) or timeout <= 0:
        raise ValueError('timeout_seconds must be finite and positive')
    components = bundle.get('components', {})
    from .components import validate
    validate(components, base, replay=replay)
    api = bundle.get('source_api')
    if api is not None:
        if (not isinstance(api, dict) or not {'component', 'rust_type'} <= set(api) or
                set(api)-{'component', 'rust_type', 'runtime'} or
                not isinstance(api['component'], str) or api['component'] not in components or not isinstance(api['rust_type'], str)):
            raise ValueError('source_api needs an admitted component and extracted Rust type')
        if 'runtime' in api and (not isinstance(api['runtime'], str) or not api['runtime'].strip()):
            raise ValueError('source_api.runtime must name a Python executable')
        component = json.loads((base/components[api['component']]).read_text())
        if component.get('language') != 'python' or not component.get('python_method'):
            raise ValueError('source_api requires an ordinary Python method component')
        selected_source = base/Path(components[api['component']]).parent/component['source']
        from .source_api import lower
        lower(selected_source.read_text(), component['function'], api['rust_type'])
    summary = request.get('contract_summary', {})
    if (not isinstance(summary, dict) or set(summary)-{'properties', 'domain', 'adaptations'} or
            any(not isinstance(v, list) or not all(isinstance(x, str) and x.strip() for x in v)
                for v in summary.values())):
        raise ValueError('contract_summary contains reviewed lists of properties, domain and adaptations')
    cache = request.get('contract_cache')
    if cache is not None:
        if not isinstance(cache, str) or not cache.strip():
            raise ValueError('contract_cache must name an explicit directory')
        request['contract_cache'] = str((base/Path(cache).expanduser()).resolve())
    runtime = request.get('rust_runtime')
    if runtime is not None and (not isinstance(runtime, str) or not re.fullmatch(r'\d+\.\d+\.\d+', runtime)):
        raise ValueError('rust_runtime must select an explicit Rust release')
    return request, selected, Application(entry, files, modules, components), []


def check_source(entry, source_api=False, imports_path=None):
    """Reconstruct the root ascription independently, binding the extracted API."""
    name = entry.replace('::', '.')
    proposition = 'Workflow.Contract.Statement Workflow.Generated.'+name
    extra = 'import Workflow.SourceAPI\n' if source_api else ''
    if source_api:
        proposition = '('+proposition+') ∧ Workflow.SourceAPI.Contract'
    imports = ''
    if imports_path is not None:
        imports = ('\n  IO.FS.writeFile '+json.dumps(str(imports_path))+
            ' (Lean.Json.arr ((← getEnv).header.moduleNames.map (fun n => Lean.Json.str n.toString))).compress')
    return f'''module

import all Workflow.Contract
import all Workflow.Proof
import Workflow.Generated.Funs
{extra.rstrip()}
meta import Lean.Util.CollectAxioms

example : {proposition} :=
  Workflow.Certificate.certificate

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← Lean.collectAxioms ``Workflow.Certificate.certificate do
    unless allowed.contains axiomName do
      throwError "Unexpected axiom {{axiomName}} in root certificate"
  logInfo "Reviewed application contract, extracted API and transitive axioms checked."{imports}
'''


def check_extracted_files(record, crate, files):
    """Reject implicit source includes outside the frozen crate file selection."""
    if record.get('has_errors') is not False:
        raise ValueError('Charon did not produce an error-free application model')
    translated = record['translated']
    if translated['crate_name'] != 'numerics_kernel':
        raise ValueError('Unexpected extracted application crate')
    selected = {(crate/name).resolve(): name for name in files}
    own_files = []
    for source in translated['files']:
        if source['crate_name'] != 'numerics_kernel':
            if source['crate_name'] not in ('core', 'std', 'alloc'):
                raise ValueError('Unadmitted external crate: '+source['crate_name'])
            continue
        name = source['name'].get('Local')
        if not isinstance(name, str) or (crate/name).resolve() not in selected:
            raise ValueError('Extracted Rust source is outside the frozen crate selection: '+str(name))
        frozen = (crate/name).resolve()
        if source['contents'] != frozen.read_text():
            raise ValueError('Extracted Rust source differs from frozen contents: '+name)
        own_files.append(selected[frozen])
    if 'src/lib.rs' not in own_files:
        raise ValueError('Missing extracted crate source identity')
    return own_files


def source_api_model(output, request):
    from .workflow import save
    api = request['rust_application'].get('source_api')
    if api is None:
        return
    component = output/'components'/api['component']
    selected = json.loads((component/'request.json').read_text())
    source = (component/selected['source']).read_text()
    from .source_api import lower
    text, description = lower(source, selected['function'], api['rust_type'])
    path = output/'lean/Workflow/SourceAPI.lean'
    if path.exists() and path.read_text() != text:
        raise ValueError('Saved scalar API model differs from the original Python source')
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    save(output/'source-api.json', description)


def check(output, request, program, runner, work, reuse=True):
    from .workflow import lean_environment, dependencies, save, sha, ROOT
    environment, build = lean_environment(output, runner, work, request)
    (output/'lean/Workflow/Check.lean').write_text(check_source(program.function,
        'source_api' in request['rust_application'], work/'model-imports.json'))
    modules = ['Workflow.Generated.Types', 'Workflow.Generated.Funs',
               *program.modules, 'Workflow.Check']
    seen, active = set(), set()
    from .proof_cache import ApplicationCache, local_imports
    foundation = {name: digest for name, digest in dependencies().items()
                  if name.startswith('Flare/') or name in ('lake-manifest.json', 'lean-toolchain')}
    foundation['aeneas_model'] = model_files(tools(request, proof_only=True)['lean_lib'])
    foundation['cache_checker'] = sha(ROOT/'scripts/numerics/proof_cache.py')
    cache = ApplicationCache(request.get('contract_cache') if reuse else None, foundation, output/'lean')

    def compile_module(module):
        if module in seen:
            return
        if module in active:
            raise ValueError('Cyclic application Lean imports: '+module)
        source = output/'lean'/Path(*module.split('.')).with_suffix('.lean')
        if not source.is_file():
            if module.startswith('Workflow.'):
                raise ValueError('Unrecorded application Lean module: '+module)
            return
        active.add(module)
        # Imports are ultimately resolved and checked by Lean, including all
        # transitive dependencies. This scan only schedules local compilation.
        for dependency in local_imports(source.read_text()):
            compile_module(dependency)
        target = build/Path(*module.split('.')).with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        if module not in ('Workflow.Proof', 'Workflow.Check') and cache.restore(source, target):
            active.remove(module)
            seen.add(module)
            return
        runner.run('lean-'+module.replace('.', '-'), ['lean', '-DautoImplicit=false',
            '-DwarningAsError=true', '-Dlinter.extra=true', '-Dlinter.missingDocs=false',
            '-o', target, source.relative_to(output/'lean')], cwd=output/'lean', env=environment)
        active.remove(module)
        seen.add(module)
        if module not in ('Workflow.Proof', 'Workflow.Check'):
            cache.save(source, target)

    for module in modules:
        compile_module(module)
    model = imported_model(tools(request, proof_only=True)['lean_lib'],
                           json.loads((work/'model-imports.json').read_text()))
    save(output/'aeneas-model.json', model)
    if cache.records:
        save(output/'proof-reuse.json', {'schema': 'numerics-proof-reuse-v1',
            'cache_enabled': cache.root is not None, 'modules': cache.records})


def extract(output, request, program, runner, work):
    from .workflow import ROOT, save, sha
    selected = tools(request)
    crate = output/'rust'
    (crate/'Cargo.toml').write_text('[package]\nname="numerics-kernel"\nversion="0.1.0"\n'
                                  'edition="2021"\n[lib]\npath="src/lib.rs"\n[workspace]\n')
    (crate/'rust-toolchain.toml').write_bytes((ROOT/'tools/numerics/rust-toolchain.toml').read_bytes())
    if request.get('rust_runtime'):
        (crate/'rust-toolchain.toml').write_text('[toolchain]\nchannel = "'+request['rust_runtime']+'"\nprofile = "minimal"\n')
    save(output/'rust-tools.json', {n: {'path': str(p),
        'sha256': sha(p) if p.is_file() else sha(p/'Aeneas.olean')} for n, p in selected.items()})
    save(output/'aeneas-model.json', model_files(selected['lean_lib']))
    runner.run('rust-version', ['rustc', '-Vv'], cwd=crate, phase='admission')
    llbc = work/'input.llbc'
    runner.run('extract', [selected['charon'], 'cargo', '--preset=aeneas', '--sysroot=default',
        '--start-from', 'numerics_kernel::'+program.function, '--dest-file='+str(llbc), '--', '--lib'],
        cwd=crate, env={'CARGO_TARGET_DIR': str(work/'native')})
    extracted = check_extracted_files(json.loads(llbc.read_text()), crate, program.files)
    save(output/'extracted-sources.json', {'schema': 'numerics-extracted-sources-v1',
                                        'crate_files': extracted})
    shutil.copyfile(llbc, output/'input.llbc')
    runner.run('translate', [selected['aeneas'], '-backend', 'lean', '-abort-on-error',
        '-warnings-as-errors', llbc, '-dest', output/'lean', '-subdir', '/Workflow/Generated',
        '-split-files', '-namespace', 'Workflow.Generated'])


def report(output, result):
    request = json.loads((output/'request.json').read_text())
    summary = request.get('contract_summary', {})
    lines = ['# Numerical verification: '+result['status'], '', result['scope'], '',
        'Lean entry: `'+result.get('entry_theorem', 'not checked')+'`.', '',
        '## Reviewed contract', '',
        *['- '+x for x in summary.get('properties', [])], '', 'Runtime domain:', '',
        *['- '+x for x in summary.get('domain', [])], '',
        'Authoritative statement: `lean/Workflow/Contract.lean`, applied to the fresh',
        'extracted API. The summary is reviewed documentation; Lean checks that statement.', '',
        *['- '+x for x in summary.get('adaptations', [])]]
    if result.get('components'):
        lines += ['', 'Numerical components:', '']
        for name, component in result['components'].items():
            lines += ['- `'+name+'`: `'+component['entry']+'`.']
            for field in component['outputs']:
                lines += ['  - '+field['name']+': checked allowance '+field['bound']+' '+field['unit']+'.']
    api = output/'source-api.json'
    if api.is_file():
        description = json.loads(api.read_text())
        lines += ['', 'Original scalar API:', '', '- Fields: '+', '.join(description['fields'])+'.',
            '- '+description['scope'], *['- '+x for x in description['assumptions']]]
    lines += ['', '## Trust boundaries', '', *['- '+x for x in result['assumptions']], '',
        'Runtime tests and sampled Python/Rust word comparisons supplement the Lean',
        'source-model proof. They do not prove compiler or hardware correctness.', '',
        '## Artifacts and reproduction', '',
        '- Production Rust crate: `rust/` (constructors, state, methods and real slice loop).',
        '- Separate runtime drivers: `drivers/`, when requested.',
        '- Lean sources: `lean/`; component evidence: `components/`, when selected.',
        '- Source/model/tool identities and commands: `result.json`, `aeneas-model.json`,',
        '  `rust-tools.json`, `runs/`. Disposable build files are removed.', '',
        'Set `FLARE_ROOT` to a compatible provider checkout and `RUN` to this directory.',
        'Build FLARE first as described in its development guide. No translator,',
        'source runtime, analyzer or LLM is needed for replay. A matching compiled',
        'Aeneas model and the pinned Lean/Mathlib build are required.', '', '```sh',
        'python3 "$FLARE_ROOT/scripts/certify_numerics.py" run --request "$REQUEST" --out "$NEW_RUN"',
        'python3 "$FLARE_ROOT/scripts/certify_numerics.py" audit --run "$RUN" --frozen',
        'python3 "$FLARE_ROOT/scripts/certify_numerics.py" replay --run "$RUN" \\',
        '  --out "$REPLAY" --aeneas-lean-lib "$AENEAS_LEAN_LIB"',
        'cargo test --manifest-path "$RUN/rust/Cargo.toml" --lib',
        'cargo test --manifest-path "$RUN/rust/Cargo.toml" --lib --release', '```', '',
        'Replay recompiles saved sources, regenerates the source API and component',
        'imports, reapplies the reviewed contract and checks the root axiom closure.',
        'The imported model manifest allows unrelated unused model build products.',
        'For a new certification, REQUEST names the reviewed request with relocated',
        'tool/runtime paths. Provider/library file identities and build pins are in',
        '`result.json` dependencies, `lean-toolchain` and `lake-manifest.json`.',
        'Transfer this entire frozen directory together; retain `result.json`.',
        *(['', 'Unresolved: '+result['error']] if 'error' in result else []), '']
    (output/'report.md').write_text('\n'.join(lines))


def certify(request_path, output):
    from .workflow import Runner, prepare as prepare_request, save, seal, sha
    started = time.monotonic()
    request, source, program, _ = prepare_request(request_path)
    base = Path(request_path).resolve().parent
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    frozen = {**request, 'rust_application': {**request['rust_application'],
                                            'files': {}, 'lean_modules': {}}}
    inputs = [{'path': str(Path(request_path).resolve()), 'sha256': sha(Path(request_path))}]
    inputs += [{'path': str((base/p).resolve()), 'sha256': sha(base/p)}
               for p in program.components.values()]
    for destination, original in program.files.items():
        target = output/'rust'/destination
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((base/original).read_bytes())
        frozen['rust_application']['files'][destination] = str(target.relative_to(output))
        inputs.append({'path': str((base/original).resolve()), 'sha256': sha(target)})
        if (base/original).resolve() == source:
            frozen['source'] = str(target.relative_to(output))
    for module, original in program.modules.items():
        target = output/'lean'/Path(*module.split('.')).with_suffix('.lean')
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((base/original).read_bytes())
        frozen['rust_application']['lean_modules'][module] = str(target.relative_to(output))
        inputs.append({'path': str((base/original).resolve()), 'sha256': sha(target)})
    if request['rust_application'].get('licenses'):
        frozen['rust_application']['licenses'] = {}
        for name, original in request['rust_application']['licenses'].items():
            target = output/'rust'/name
            target.write_bytes((base/original).read_bytes())
            frozen['rust_application']['licenses'][name] = str(target.relative_to(output))
            inputs.append({'path': str((base/original).resolve()), 'sha256': sha(target)})
    save(output/'request.json', frozen)
    save(output/'program.json', program.record())
    result = {'schema': 'numerics-run-v1', 'profile': 'rust-application-proof-v1',
        'status': 'unresolved', 'completed_stages': ['source_admitted'],
        'request_path': str(Path(request_path).resolve()),
        'source_path': str(source), 'source_sha256': sha(output/frozen['source']),
        'source_language': 'rust', 'target': 'rust-aeneas', 'application_inputs': inputs,
        'scope': 'The frozen multi-module Rust API '+program.function+
                 ', against its separately reviewed Lean contract.',
        'assumptions': [
            'The authored Lean contract, exact reference and engineering domain require review.',
            'Charon/Aeneas translation, including the recorded UInt64 cast patch, is a source-model trust boundary.',
            'The selected Rust compiler/runtime implements separate nearest/even binary64 operations with gradual underflow; compiler and hardware fidelity are not proved.',
            'Arithmetic bounds exclude physical sensor/model uncertainty.']}
    if 'source_api' in request['rust_application']:
        result['assumptions'].insert(1, 'The ordinary Python scalar AST mapping and scalar NumPy constructor specialization are a frontend trust boundary; this is not a verified Python interpreter.')
    runner = Runner(output, request.get('timeout_seconds', 240))
    work = output/'.work'
    work.mkdir()
    try:
        if program.components:
            from .components import generate
            runner.last_stage = 'components'
            result['components'] = generate(base, output, program.components)
            result['completed_stages'].append('components_certified')
            frozen['rust_application']['components'] = {
                name: 'components/'+name+'/request.json' for name in program.components}
            save(output/'request.json', frozen)
        source_api_model(output, request)
        extract(output, request, program, runner, work)
        result['completed_stages'].append('rust_extracted')
        check(output, request, program, runner, work)
        result['completed_stages'].append('lean_root_checked')
        result['entry_theorem'] = 'Workflow.Certificate.certificate'
        # Runtime checks are diagnostics; never substitute for the root proof.
        for mode in ('debug', 'release'):
            runner.run('rust-tests-'+mode, ['cargo', 'test', '--lib',
                *(['--release'] if mode == 'release' else [])], cwd=output/'rust',
                env={'CARGO_TARGET_DIR': str(work/'tests')}, phase='diagnostic')
        from .api_diagnostics import run as api_diagnostics
        diagnostic = api_diagnostics(output, request, runner, work)
        if diagnostic is not None:
            result['api_diagnostics'] = diagnostic
        result['completed_stages'].append('runtime_diagnostics')
        result['status'] = 'certified'
    except (RuntimeError, ValueError, OSError) as error:
        result.update(error=str(error), failure_stage=getattr(runner, 'last_stage', 'admission'))
        result['failure_kind'] = error.kind if isinstance(error, ToolError) else 'stage_rejected'
        record = output/'runs'/result['failure_stage']/'run.json'
        if record.is_file() and json.loads(record.read_text())['status'] == 'timeout':
            result['failure_kind'] = 'timeout'
    finally:
        result['elapsed_seconds'] = time.monotonic()-started
        report(output, result)
        shutil.rmtree(work)
        seal(output, result)
    return result


def replay(path, output, aeneas_lean_lib=None):
    from .workflow import Runner, prepare as prepare_request, save
    request, _, program, _ = prepare_request(path/'request.json', replay=True)
    original = json.loads((path/'result.json').read_text())
    if 'lean_root_checked' not in original.get('completed_stages', []):
        raise ValueError('This application has no checked Lean root to replay')
    if aeneas_lean_lib is not None:
        request['rust_tools'] = {**request.get('rust_tools', {}), 'lean_lib': str(Path(aeneas_lean_lib).resolve())}
    if not matching_model(tools(request, proof_only=True)['lean_lib'], json.loads((path/'aeneas-model.json').read_text())):
        raise ValueError('Replay needs the recorded Aeneas Lean model')
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    shutil.copytree(path/'lean', output/'lean')
    shutil.copytree(path/'rust', output/'rust')
    shutil.copyfile(path/'request.json', output/'request.json')
    if program.components:
        shutil.copytree(path/'components', output/'components')
        from .components import materialize
        materialize(output, program.components)
    source_api_model(output, request)
    runner = Runner(output, request.get('timeout_seconds', 240))
    work = output/'.work'
    work.mkdir()
    try:
        check(output, request, program, runner, work, reuse=False)
        recorded = json.loads((path/'aeneas-model.json').read_text())
        if recorded.get('schema') == 'numerics-imported-model-v1' and recorded != json.loads((output/'aeneas-model.json').read_text()):
            raise ValueError('Replay loaded a different Aeneas module closure')
    finally:
        shutil.rmtree(work)
    result = {'status': 'replayed', 'certificate_status': original['status'],
              'entry_theorem': 'Workflow.Certificate.certificate',
              'qualification': 'Fresh Lean replay; no Rust translator, producer, runtime or LLM invoked.'}
    save(output/'replay.json', result)
    return result
