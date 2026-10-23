"""Staged numerical certification; language, analysis and target contracts are separate."""
from fractions import Fraction as Q
import hashlib
import json
import os
import math
import shutil
import re
import time
from pathlib import Path
import subprocess
import sys

from .analysis import analyze
from .emit import kernel_source, proof_source
from .frontend import FRONTENDS, Unsupported, parse
from .specification import validate as validate_specification, describe as describe_specification

ROOT = Path(__file__).resolve().parents[2]
BACKENDS = {"lean-flare": "Checked compositional binary64 contracts using existing FLARE lemmas"}
TARGETS = {"lean": "Lean certificate without a Rust port", "rust-aeneas": "Rust f64 source and fresh Charon/Aeneas Lean extraction"}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, data):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(json.dumps(data, indent=2) + '\n')


def prepare(path, *, replay=False):
    path = Path(path).resolve()
    request = json.loads(path.read_text())
    if not isinstance(request, dict) or request.get('schema') != 'numerics-request-v1':
        raise ValueError('Expected schema numerics-request-v1')
    for field in ['source', 'function']:
        if not isinstance(request.get(field), str) or not request[field].strip():
            raise ValueError('Missing source selection: '+field)
    for field, default in [('language', 'python'), ('backend', 'lean-flare'), ('target', 'lean')]:
        if not isinstance(request.get(field, default), str):
            raise ValueError('Expected string selector: '+field)
    source = (path.parent / request['source']).resolve()
    if 'rust_application' in request:
        from .application import prepare as prepare_application
        return prepare_application(path, request, replay=replay)
    program = parse(request.get('language', 'python'), source.read_text(), request['function'], request.get('python_method'), request.get('python_arrays'),request.get('python_branches'),request.get('python_counted'),request.get('scientific_arrays'))
    if program.scientific:
        if request.get('producer','lean-flare')!='lean-flare' or request.get('proof'):
            raise Unsupported('Scientific arrays currently use automatic lean-flare validation')
        if request.get('target','lean')=='rust-aeneas' and (not request.get('rust_port') or len(program.outputs)>2):
            raise Unsupported('Scientific Rust delivery requires a retained API port with at most two output cells')
    if program.c:
        from .c_emit import memory_profile
        if request.get('producer','lean-flare')!='lean-flare' or request.get('proof'):
            raise Unsupported('The C profile currently uses automatic lean-flare validation')
        if memory_profile(program) and request.get('target','lean')!='lean':
            raise Unsupported('C buffer roots currently use Lean delivery; Rust memory bridges need application support')
    if program.counted and (request.get('target','lean')!='lean' or request.get('proof') or
            request.get('producer','lean-flare')!='lean-flare'):
        raise Unsupported('Counted source currently uses Lean and the lean-flare producer')
    if program.branches and (request.get('target', 'lean') != 'lean' or request.get('proof') or
            request.get('producer', 'lean-flare') not in ('lean-flare', 'precisa')):
        raise Unsupported('Conditional profile currently uses Lean and the lean-flare or precisa producer')
    if program.branches and program.branches['schema']=='python-guard-local-v1' and request.get('producer','lean-flare')!='lean-flare':
        raise Unsupported('Guard-local branches currently use the lean-flare producer')
    if program.arrays and (request.get('target','lean') != 'lean' or request.get('proof') or request.get('producer','lean-flare') != 'lean-flare'):
        raise Unsupported('The fixed-array profile currently uses Lean certification with the lean-flare producer')
    from .runtimes import validate_selection
    validate_selection(program, request.get('source_runtime'))
    questions = []
    domain = request.get('domain', {})
    if not isinstance(domain, dict):
        raise ValueError('domain must map input names to ranges')
    for name in program.inputs:
        if name not in domain:
            questions.append({'field': 'domain.' + name, 'question': f'What finite input range [lower, upper] is valid for {name}?'})
        else:
            if not isinstance(domain[name], list) or len(domain[name]) != 2:
                raise ValueError('Each domain entry must be an exact-rational [lower, upper] pair')
            if any(not isinstance(x, str) for x in domain[name]):
                raise ValueError('Use exact-rational strings for input bounds')
            lo, hi = map(Q, domain[name])
            if lo > hi:
                raise ValueError('Reversed input range: ' + name)
    if set(domain) - set(program.inputs):
        raise ValueError('Unknown input domain names')
    targets = request.get('outputs', [])
    if not isinstance(targets, list):
        raise ValueError('outputs must be a list in return order')
    if len(targets) != len(program.outputs):
        questions.append({'field': 'outputs', 'question': f'Provide {len(program.outputs)} output names, units and desired absolute error limits in return order.'})
    else:
        for i, target in enumerate(targets):
            if not isinstance(target, dict):
                raise ValueError('Each output needs a name, unit and limit')
            for field in ['name', 'unit', 'limit']:
                if not target.get(field):
                    questions.append({'field': f'outputs.{i}.{field}', 'question': f'What is output {i+1} {field}?'})
                elif not isinstance(target[field], str) or not target[field].strip():
                    raise ValueError('Output '+field+' must be a nonempty string')
            if target.get('limit') and not isinstance(target['limit'], str):
                raise ValueError('Use exact-rational strings for error limits')
            if target.get('limit') and Q(target['limit']) <= 0:
                raise ValueError('Error limits must be positive exact rationals')
    if request.get('backend', 'lean-flare') not in BACKENDS:
        raise Unsupported('No admitted analysis/checker backend for this request')
    if request.get('target', 'lean') not in TARGETS:
        raise Unsupported('No admitted deployment target for this request')
    specification = request.get('specification')
    if specification is None or (isinstance(specification,list) and len(specification)!=len(program.outputs)):
        questions.append({'field': 'specification', 'question': 'What independent exact mathematical expressions should the outputs implement? Provide one expression per output using original input names.'})
    else:
        validate_specification(specification,program)
    timeout = request.get('timeout_seconds', 120)
    if type(timeout) not in (int, float) or not math.isfinite(timeout) or timeout <= 0:
        raise ValueError('timeout_seconds must be finite and positive')
    cache = request.get('contract_cache')
    if cache is not None:
        if not isinstance(cache, str) or not cache.strip():
            raise ValueError('contract_cache must name an explicit cache directory')
        request['contract_cache'] = str((path.parent/Path(cache).expanduser()).resolve())
    port = request.get('rust_port')
    if port is not None:
        if (request.get('target') != 'rust-aeneas' or request.get('language') == 'rust' or
                not isinstance(port, dict) or
                set(port) != {'source', 'function', 'proof_source', 'equivalence'}):
            raise ValueError('rust_port requires a non-Rust source, rust-aeneas target, source, function, proof_source and equivalence')
        for field in ['source', 'proof_source']:
            if not isinstance(port[field], str) or not (path.parent/port[field]).is_file():
                raise ValueError('Missing rust_port file: '+field)
        for field in ['function', 'equivalence']:
            pattern = r'[A-Za-z_][A-Za-z_0-9]*' if field == 'function' else r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*'
            if not isinstance(port[field], str) or not re.fullmatch(pattern, port[field]):
                raise ValueError('Invalid rust_port declaration: '+field)
    authored = request.get('proof')
    if authored is not None:
        if not isinstance(authored, dict) or set(authored)-{'source','accuracy','specification_equiv','bounds'}:
            raise ValueError('proof needs source, accuracy, bounds and optional specification_equiv')
        if not isinstance(authored.get('source'), str):
            raise ValueError('proof.source must name a saved authored Lean module')
        for field in ['accuracy','specification_equiv']:
            if field in authored and not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', authored[field]):
                raise ValueError('Invalid authored proof declaration: '+field)
        if not authored.get('accuracy'):
            raise ValueError('proof.accuracy is required')
        if not isinstance(authored.get('bounds'), list) or len(authored['bounds']) != len(program.outputs):
            raise ValueError('proof.bounds must list an exact nonnegative rational per output')
        if any(not isinstance(x,str) or Q(x)<0 for x in authored['bounds']):
            raise ValueError('proof bounds must be nonnegative exact-rational strings')
    from .integration import validate
    validate(request, program, require_adapters=not replay)
    return request, source, program, questions


class Runner:
    def __init__(self, output, timeout=120):
        self.output = output
        self.timeout = timeout

    def run(self, label, command, cwd=ROOT, env=None, phase='check', inherit_developer_dir=False):
        self.last_stage = label
        command = list(map(str, command))
        overrides = dict(env or {})
        if sys.platform == 'darwin' and not inherit_developer_dir:
            overrides.setdefault('DEVELOPER_DIR', os.environ.get('DEVELOPER_DIR', '/Library/Developer/CommandLineTools'))
        invocation = [sys.executable, str(ROOT/'scripts/tool_integration_run.py'),
            '--output', str(self.output/'runs'/label), '--phase', phase,
            '--timeout', str(self.timeout), '--cwd', str(cwd)]
        for name, value in overrides.items():
            invocation += ['--env', name+'='+value]
        result = subprocess.run([*invocation, '--', *command], check=False, stdout=subprocess.PIPE, text=True)
        sys.stderr.write(result.stdout)
        if result.returncode:
            raise RuntimeError('Stage failed; retained command: ' + label)
        return (self.output/'runs'/label/'stdout.txt').read_text()



def dependencies():
    files = [ROOT/'lake-manifest.json', ROOT/'lean-toolchain',
             ROOT/'scripts/certify_numerics.py', ROOT/'scripts/tool_integration_run.py',
             *sorted((ROOT/'Flare').rglob('*.lean')),
             *sorted((ROOT/'scripts/numerics').glob('*.py')),
             *sorted((ROOT/'tools/numerics').glob('*'))]
    return {str(p.relative_to(ROOT)): sha(p) for p in files}


def seal(output, result):
    result['dependencies'] = dependencies()
    result['artifacts'] = {str(p.relative_to(output)): sha(p) for p in sorted(output.rglob('*'))
        if p.is_file() and '.work' not in p.parts and p != output/'result.json'}
    save(output/'result.json', result)


def report(output, result):
    lines = ['# Numerical verification: '+result['status'], '', result['scope'], '',
             'Lean entry: `'+result.get('entry_theorem','not checked')+'`.', '',
             'Original-input domain:']
    request = json.loads((output/'request.json').read_text())
    lines += [f'- {name}: [{limits[0]}, {limits[1]}], finite binary64.'
              for name, limits in request['domain'].items()]
    if request.get('python_method'):
        binding = request['python_method']
        lines += ['', 'Selected Python method: `'+request['function']+'`.',
                  'State attributes: '+', '.join(k+' ← '+v for k,v in binding['state'].items())+'.',
                  'Fixed binary64 attributes (exact hexadecimal values):']
        lines += ['- '+name+': '+value.hex() for name,value in binding['constants'].items()]
        lines += ['Ordered measurements: '+', '.join(binding['sequence'])+'.']
    if request.get('python_arrays'):
        lines += ['', 'Built-in Python list input shapes: `'+json.dumps(request['python_arrays'])+'`.',
                  'Inputs are read-only; returned storage is fresh. The Lean root checks the shape guard and the original ascending product schedule.']
    if result.get('scientific_arrays'):
        profile=result['scientific_arrays']
        lines += ['', 'Scientific API: `'+request['function']+'`; runtime profile `'+profile['runtime']+'`.']
        lines += ['- `'+field['name']+'`: '+(str(field['shape']) if field['shape'] else 'scalar') for field in profile['inputs']]
        lines += ['Return shapes: `'+json.dumps(profile['outputs'])+'`, in API order; fresh collection storage. Input shapes and result dimensions/cell counts are part of the Lean root.']
    if result.get('c_api'):
        lines += ['', 'Selected C API: `'+request['function']+'`.']
        for parameter in result['c_api']:
            if parameter['kind']=='buffer':
                lines += ['- `'+parameter['name']+'`: '+str(parameter['length'])+' initialized double cells; '+
                          ('read-only' if parameter['readonly'] else 'writable')+'.']
        if any(p['kind']=='buffer' for p in result['c_api']):
            lines += ['Caller contract: valid object extents and separation of each writable region from every other buffer. Read-only regions may overlap.']
        if 'c_source_conditions_checked' in result.get('completed_stages',[]):
            lines += ['The Lean root includes source-derived access/counter conditions and, for buffers, successful typed-heap execution and unchanged cells outside the writable region. See c-vcs.json and lean/Workflow/Check.lean.']
    lines += ['', 'Independent exact specification:']
    lines += ['- '+x for x in describe_specification(request['specification'])]
    lines += ['', 'Allowances:']
    for target in result.get('outputs',[]):
        lines += [f"- {target['name']}: {target['evidence']} {target['bound']} {target['unit']}; "
                  f"requested {target['limit']}; meets budget: {target['meets_budget']}."]
    lines += ['', 'Trust boundaries:'] + ['- '+x for x in result['assumptions']]
    if 'producer' in result:
        lines += ['', 'Producer: `'+result['producer']+'`.']
    if result.get('producer_validation') == 'lean-scalar-interval-v1':
        lines += ['Validation: reusable scalar inference with native nearest rounding, checked polynomial rewrites, exact rational enclosure rules and interval subdivision.',
                  'Acceptance requires Lean to prove the proposed allowance itself. See analysis.json for each input box and rounding allowance.']
    if result.get('producer_validation') == 'lean-conditional-four-flows-v1':
        lines += ['Validation: Lean checks all four native/exact branch choices, including divergent flows; no stability assumption is used.',
                  'Both arms have checked finite arithmetic and denominator premises on the full input domain.']
        if result.get('claim_policy') == 'producer-output-claims':
            lines += ['The actual maximum stable/unstable candidate is the Lean proof target; foreign proof files remain untrusted evidence.']
        else:
            lines += ['The proposed allowance is the requested budget, independently proved in Lean.']
    if result.get('producer_validation') == 'lean-guard-local-v1':
        lines += ['Validation: native/exact agreement of the direct finite-input guard is proved in Lean.',
                  'Only the selected arm is evaluated; arithmetic and denominator premises are checked on its guard domain.']
    if result.get('producer_validation') == 'lean-counted-invariant-v1':
        lines += ['Validation: one initialized and preserved native/exact invariant is proved for every natural iteration count.',
                  'The root instantiates '+str(request['python_counted']['iterations'])+' iterations of the actual source loop; incoming error is retained.',
                  'The allowance is a checked uniform invariant bound, not an estimate of the attained error.']
    if result.get('claim_policy') == 'requested-budgets':
        lines += ['Foreign proof output and sharper printed bounds remain untrusted evidence.',
                  'The selected allowance is the requested budget; acceptance requires an independent Lean proof.',
                  'See evidence.json for raw candidates, tool identities and validation roles.']
    if 'error' in result:
        lines += ['', 'Unresolved: '+result['error']]
    lines += ['', 'Artifact/freshness auditing is not proof checking. Replay recompiles the saved',
              'Lean sources and an independently reconstructed root-type/axiom check.']
    (output/'report.md').write_text('\n'.join(lines)+'\n')


def lean_environment(output, runner, work, request):
    keys = ['LEAN_PATH','LEAN_SRC_PATH','PATH','LD_LIBRARY_PATH','DYLD_LIBRARY_PATH','LEAN_SYSROOT']
    code = 'import os,json;print(json.dumps({k:os.environ[k] for k in '+repr(keys)+' if k in os.environ}))'
    environment = json.loads(runner.run('lean-environment', ['lake','env',sys.executable,'-c',code]))
    paths = []
    if request.get('target','lean') == 'rust-aeneas':
        from .rust import tools
        paths.append(str(tools(request, proof_only=True)['lean_lib']))
    build = work/'build'; build.mkdir(parents=True)
    paths += [str(build),environment['LEAN_PATH']]
    environment['LEAN_PATH'] = os.pathsep.join(paths)
    environment['LEAN_SRC_PATH'] = str(output/'lean')+os.pathsep+environment.get('LEAN_SRC_PATH','')
    return environment, build


def check_lean(output, request, program, bounds, runner, work, reuse=True):
    from .emit import check_source
    environment, build = lean_environment(output, runner, work, request)
    with_rust = request.get('target','lean') == 'rust-aeneas'
    modules = []
    if with_rust:
        modules += [('types','Workflow/Generated/Types.lean'),('functions','Workflow/Generated/Funs.lean')]
    adapter_module = output/'validation.json'
    if adapter_module.exists():
        validation = json.loads(adapter_module.read_text())
        if validation.get('schema') != 'numerics-validation-v1' or validation.get('kind') != 'adapter-lean-module':
            raise ValueError('Unsupported adapter Lean validation record')
        for index, name in enumerate(validation.get('modules', [])):
            if not isinstance(name, str) or not re.fullmatch(r'Workflow/(?:[A-Za-z_][A-Za-z_0-9]*/)*[A-Za-z_][A-Za-z_0-9]*\.lean', name):
                raise ValueError('Invalid adapter module path')
            modules += [('contract-'+str(index), name)]
    modules += [('kernel','Workflow/Kernel.lean')]
    if request.get('rust_port'):
        modules += [('rust-equivalence','Workflow/RustEquiv.lean')]
    if request.get('proof') or adapter_module.exists():
        modules += [('authored','Workflow/Authored.lean')]
    modules += [('proof','Workflow/Proof.lean')]
    (output/'lean/Workflow/Check.lean').write_text(check_source(program,request['domain'],bounds,
                                                             request['outputs'],with_rust))
    modules += [('root-check','Workflow/Check.lean')]
    from .proof_cache import ProofCache
    foundation = {name: digest for name,digest in dependencies().items()
                  if name.startswith('Flare/') or name in {'lake-manifest.json','lean-toolchain'}}
    cache = ProofCache(request.get('contract_cache') if reuse else None, foundation, output/'lean')
    for label,module in modules:
        target = build/Path(module).with_suffix('.olean'); target.parent.mkdir(parents=True,exist_ok=True)
        reusable = label.startswith('contract-')
        if reusable and cache.restore(output/'lean'/module, target):
            continue
        runner.run('lean-'+label, ['lean','-DautoImplicit=false','-DwarningAsError=true',
            '-Dlinter.extra=true','-Dlinter.missingDocs=false','-o',target,module],
            cwd=output/'lean',env=environment)
        if reusable:
            cache.save(output/'lean'/module, target)
    if cache.records:
        save(output/'proof-reuse.json', {'schema':'numerics-proof-reuse-v1', 'cache_enabled':cache.root is not None,
                                      'modules':cache.records})


def output_bounds(program, request):
    from .analysis import Bound
    if request.get('proof'):
        return {n:Bound(Q(0),Q(0),Q(0),Q(e))
                for n,e in zip(program.outputs,request['proof']['bounds'],strict=True)}, []
    return analyze(program,request['domain'])


def kernel_for_run(output, request, program):
    if program.scientific:
        from .scientific_emit import model_source
        return model_source(program,request,(output/request['source']).read_text())
    if program.c:
        from .c_emit import model_source, verification_conditions
        saved=output/'c-vcs.json'
        if saved.exists() and json.loads(saved.read_text())!=verification_conditions(program):
            raise ValueError('Saved C verification conditions do not match the frozen source')
        return model_source(program,request)
    if program.branches and program.branches['schema']=='python-guard-local-v1':
        from .branch_local import model_source
        return model_source(program,request,output)
    if program.counted:
        from .counted import model_source
        from .composition import identity, function_module
        from .counted import local_program
        local=local_program(program); key=identity(local.record())
        saved=output/'lean/Workflow/Functions'/('F'+key+'.lean')
        if saved.read_text()!=function_module(local,key):
            raise ValueError('Saved counted helper does not match frozen source')
        return model_source(program,request)
    if program.arrays:
        from .array_emit import kernel_source as array_kernel_source
        return array_kernel_source(program,request,(output/request['source']).read_text())
    layout_path = output/'model-layout.json'
    if not layout_path.exists():
        return kernel_source(program,request['specification'])
    from .composition import function_module, groups, identity, local_program, model_source
    layout = json.loads(layout_path.read_text())
    expected = groups(program, (output/request['source']).read_text(), request)
    if (layout.get('schema') != 'numerics-helper-layout-v1' or expected is None or
            layout.get('calls') != json.loads(json.dumps(expected))):
        raise ValueError('Saved model layout does not match original source helper boundaries')
    for call in expected:
        local, _, _ = local_program(program, call)
        key = identity(local.record())
        source = output/'lean/Workflow/Functions'/('F'+key+'.lean')
        if source.read_text() != function_module(local, key):
            raise ValueError('Saved helper function does not match the frozen source graph')
    return model_source(program,request['specification'],expected)


def certify(request_path, output):
    selection = json.loads(Path(request_path).read_text())
    if isinstance(selection, dict) and 'rust_application' in selection:
        from .application import certify as certify_application
        return certify_application(request_path, output)
    started = time.monotonic()
    request, source, program, questions = prepare(request_path)
    if questions:
        return {'status':'needs_input','questions':questions}
    output = Path(output).resolve(); output.mkdir(parents=True,exist_ok=False)
    frozen_source = source.read_bytes()
    if parse(request.get('language','python'),frozen_source.decode(),request['function'],request.get('python_method'),request.get('python_arrays'),request.get('python_branches'),request.get('python_counted'),request.get('scientific_arrays')) != program:
        raise ValueError('Source changed during admission; start a fresh run')
    source_name = 'source'+source.suffix
    frozen_request = {**request,'source':source_name}
    if request.get('proof'):
        authored = (Path(request_path).resolve().parent/request['proof']['source']).resolve()
        frozen_request['proof'] = {**request['proof'],'source':'lean/Workflow/Authored.lean'}
        p=output/'lean/Workflow/Authored.lean'; p.parent.mkdir(parents=True); p.write_bytes(authored.read_bytes())
    port_sources = {}
    if request.get('rust_port'):
        port = request['rust_port']
        frozen_port = dict(port)
        for field, filename in [('source', 'rust-port.rs'), ('proof_source', 'lean/Workflow/RustEquiv.lean')]:
            original = (Path(request_path).resolve().parent/port[field]).resolve()
            target = output/filename
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(original.read_bytes())
            frozen_port[field] = filename
            port_sources[field] = {'path': str(original), 'sha256': sha(target)}
        frozen_request['rust_port'] = frozen_port
    save(output/'request.json',frozen_request)
    (output/source_name).write_bytes(frozen_source)
    save(output/'program.json',program.record())
    with_rust = request.get('target','lean') == 'rust-aeneas'
    result = {'schema':'numerics-run-v1','status':'unresolved','completed_stages':['source_admitted'],
        'source_path':str(source),'source_sha256':sha(output/source_name),
        'source_language':program.language,'target':request.get('target','lean'),
        'scope':'One bounded source computation on original finite scalar binary64 inputs in the supplied domain.',
        'assumptions':[
            'The admitted frontend maps the original source to the ordered binary64 graph; its implementation is trusted.',
            'The selected runtime/compiler/hardware implements separate nearest/even binary64 operations with gradual underflow, no FMA or reassociation.',
            'The exact specification and engineering domain require review. Physical/model uncertainty and calls beyond this frozen bounded computation are excluded.'],
        'source_assurance':FRONTENDS[program.language].assurance}
    if request.get('python_method'):
        result['scope']='A frozen finite horizon of the selected original Python method body on the configured scalar state and fixed binary64 attributes.'
        result['assumptions'].append('The caller invokes the selected original method body on an ordinary instance with the configured scalar fields and omitted optional gains. Module initialization, construction and dynamic dispatch are outside this certificate.')
    if program.branches:
        result['scope'] = 'One terminal Python scalar conditional, including divergent native/exact branch choices on original finite binary64 inputs.'
        if program.branches['schema']=='python-guard-local-v1':
            result['scope']='One input-guarded scalar conditional with proved native/exact guard agreement and branch-local arithmetic premises.'
            result['assumptions'].append('The admitted direct input comparison selects the only evaluated scalar arm; general control flow and computed floating-point guards are outside this local-domain profile.')
        else:
            result['assumptions'].append('Both arms use admitted total finite scalar arithmetic on this domain; custom dispatch and general control flow are excluded. No branch-stability assumption is introduced.')
    if program.counted:
        result['scope']='A counted Python two-state helper loop, with a preserved native/exact invariant proved for all natural horizons and instantiated at the selected count.'
        result['assumptions'].append('The selected nonnegative integer count and ordinary scalar helper API are mapped to the compact fold by the admitted frontend; compiler/runtime correspondence remains trusted.')
    if program.scientific:
        result['scope']='One closed fixed-shape scientific array API with explicit dtype, checked collection execution/shapes/accesses and independent exact collection algebra.'
        result['scientific_arrays']=program.scientific
        result['source_assurance']='Closed scientific collection profile: source/library mapping, native double operations, ordinary container representation and compiler/runtime fidelity are trusted; Lean checks typed shapes, model execution, finite values, exact-reference accuracy and budgets.'
        result['assumptions'].append('Inputs are ordinary native-endian binary64 NumPy ndarrays with C-contiguous input storage, or Julia Vector{Float64} values, plus binary64 scalars, with the declared shapes and no custom dispatch. The floating-error policy is nontrapping; warning/status flags are outside the numerical theorem. Inputs are read-only and returned collection storage is fresh. Source parsing, library-primitive mapping, runtime and compiler/hardware fidelity remain trusted. No BLAS, fused broadcast or arbitrary reduction contract is claimed.')
    if program.c:
        result['scope']='One admitted C11 binary64 API, with source-derived access/counter conditions, checked abstract heap execution for buffers, and independent numerical allowances.'
        result['c_api']=program.c['api']
        result['assumptions'].append('Buffer regions represent live, initialized, correctly aligned C double objects. The caller establishes their extents and required separation; source parsing, typed-cell representation and compiler fidelity remain trusted. Floating-point status flags are outside the contract.')
    if program.arrays:
        result['scope']='One fixed-shape built-in Python list matrix/vector product, with checked shape guard, finite execution and entrywise numerical bounds relative to an independent real matrix specification.'
        result['array_shapes']=program.arrays
        result['assumptions'].append('Original inputs are built-in lists of built-in binary64 floats. The admitted AST-to-persistent-Lean-array mapping is trusted; inputs are read-only and outputs use fresh independent storage. No NumPy or BLAS correspondence is claimed.')
    if port_sources:
        result['rust_port_sources'] = port_sources
    if with_rust:
        result['assumptions'].append('Charon/Aeneas translation and its Float model are declared source-model trust boundaries; no machine-code compiler proof is claimed.')
    if request.get('proof'):
        result['authored_source'] = {'path':str(authored),'sha256':sha(output/'lean/Workflow/Authored.lean')}
    runner = Runner(output,request.get('timeout_seconds',120)); work = output/'.work'; work.mkdir()
    try:
        if (sys.float_info.radix,sys.float_info.mant_dig,sys.float_info.max_exp,sys.float_info.rounds)!=(2,53,1024,1):
            raise ValueError('Host does not report the admitted nearest/even binary64 profile')
        tiny=float.fromhex('0x0.0000000000001p-1022')
        if tiny*1.0 != tiny:
            raise ValueError('Host preflight does not preserve subnormals')
        save(output/'host.json',{'python':sys.version,'subnormal_probe_passed':True,
            'qualification':'Runtime admission diagnostics, not a hardware proof.'})
        from .runtimes import admit_runtime
        runner.last_stage='source-runtime-admission'
        runtime=admit_runtime(program,request,output,work,runner)
        result['source_runtime']=runtime['kind']; result['completed_stages'].append('source_runtime_admitted')
        runner.last_stage='analysis'
        from .integration import Session
        session = Session(program, request, output, work, runner, output_bounds, source_name)
        producer = request.get('producer', 'lean-flare')
        result['producer'] = producer
        proposal_started = time.monotonic()
        proposal = session.execute(producer, 'producer')
        result['proposal_seconds'] = time.monotonic()-proposal_started
        summaries, steps, bounds = proposal.summaries, proposal.steps, proposal.claims
        authored = session.proof_module(proposal)
        if proposal.layout is not None:
            result['assumptions'].append('The helper layout structurally groups the admitted graph without changing its ordered operations; frontend/model generation remains a source-correspondence trust boundary.')
        result['producer_validation'] = proposal.details.get('validation', 'lean-root')
        result['claim_policy'] = proposal.details.get('claim_policy', 'producer-output-claims')
        save(output/'analysis.json',{'producer':producer, 'steps':steps,
            'candidate_bounds':{n:str(bounds[n].e) for n in program.outputs},
            'derivation_bounds':{n:str(summaries[n].e) for n in program.outputs},
            'producer_details':proposal.details})
        result['completed_stages'].append('bounds_proposed')
        result['outputs']=[{'name':t['name'],'unit':t['unit'],'limit':str(Q(t['limit'])),
            'bound':str(bounds[n].e),'meets_budget':bounds[n].e<=Q(t['limit']),'evidence':'proposed'}
            for n,t in zip(program.outputs,request['outputs'],strict=True)]
        if with_rust:
            runner.last_stage='rust-tool-admission'
            session.execute('rust-aeneas', 'extractor', source=frozen_source)
            result['completed_stages'].append('rust_source_extracted')
        lean=output/'lean/Workflow'; lean.mkdir(parents=True,exist_ok=True)
        if program.c:
            from .c_emit import verification_conditions
            save(output/'c-vcs.json',verification_conditions(program))
        (lean/'Kernel.lean').write_text(kernel_for_run(output,frozen_request,program))
        (lean/'Proof.lean').write_text(proof_source(program,request['domain'],summaries,steps,
                                                  request['outputs'],with_rust,authored,
                                                  isinstance(request['specification'],dict),
                                                  request.get('rust_port',{}).get('equivalence'),
                                                  bounds if producer != 'lean-flare' or authored else None))
        session.execute('lean-root', 'validator', bounds=bounds)
        record=json.loads((output/'analysis.json').read_text())
        record['accepted_bounds']={n:str(bounds[n].e) for n in program.outputs}
        save(output/'analysis.json',record)
        result['entry_theorem']='Workflow.Certificate.certificate'
        result['completed_stages'].append('lean_root_checked')
        result['completed_stages'].append('source_numerics_checked')
        if program.c: result['completed_stages'].append('c_source_conditions_checked')
        for target in result['outputs']: target['evidence']='checked'
        from .diagnostics import diagnose
        runner.last_stage='source-diagnostics'
        result['diagnostics']=diagnose(program,frozen_source.decode(),request,output,work,runner,runtime,with_rust)
        result['completed_stages'].append('source_diagnostics_checked')
        result['status']='certified' if all(t['meets_budget'] for t in result['outputs']) else 'budget_not_met'
    except (RuntimeError,ValueError,OSError) as error:
        result['error']=str(error)
        result['failure_stage']=getattr(runner,'last_stage','admission_or_analysis')
        if hasattr(error, 'kind'):
            result['failure_kind'] = error.kind
        record_path=output/'runs'/result['failure_stage']/'run.json'
        if record_path.is_file() and 'failure_kind' not in result:
            stage=json.loads(record_path.read_text())
            diagnostic=(record_path.parent/'stdout.txt').read_text()
            if stage['status']=='timeout': result['failure_kind']='timeout'
            elif 'maximum number of heartbeats' in diagnostic: result['failure_kind']='heartbeats'
            else: result['failure_kind']='stage_rejected'
        elif result['failure_stage']=='analysis': result['failure_kind']='analysis_gap'
    finally:
        result['elapsed_seconds']=time.monotonic()-started
        report(output,result); shutil.rmtree(work)
        seal(output,result)
    return result


def audit_run(path, frozen=False):
    """Identity/freshness audit only; never substitute it for Lean replay."""
    path=Path(path).resolve(); result=json.loads((path/'result.json').read_text())
    for name,digest in result['artifacts'].items():
        source=(path/name).resolve()
        if not source.is_relative_to(path) or not source.is_file() or sha(source)!=digest:
            raise ValueError('Changed or missing artifact: '+name)
    if not frozen:
        if sha(result['source_path'])!=result['source_sha256']:
            raise ValueError('Original source changed; regenerate the certificate')
        for name,digest in result.get('dependencies',{}).items():
            if sha(ROOT/name)!=digest:
                raise ValueError('Workflow/library dependency changed: '+name)
        if 'authored_source' in result:
            authored=result['authored_source']
            if sha(authored['path'])!=authored['sha256']:
                raise ValueError('Authored proof source changed; regenerate the certificate')
        for record in result.get('rust_port_sources', {}).values():
            if sha(record['path']) != record['sha256']:
                raise ValueError('Rust port or equivalence proof source changed; regenerate the certificate')
        for record in result.get('application_inputs', []):
            if sha(record['path']) != record['sha256']:
                raise ValueError('Application source, contract or proof changed: '+record['path'])
        if 'source-runtime.json' in result['artifacts']:
            runtime=json.loads((path/'source-runtime.json').read_text())
            for library in runtime.get('libraries',[]):
                for file,digest in library['files'].items():
                    if sha(file)!=digest:raise ValueError('Source runtime library changed: '+file)
            if sha(runtime['executable'])!=runtime['executable_sha256']:
                raise ValueError('Source runtime executable changed; regenerate diagnostics and certificate')
        if 'evidence.json' in result['artifacts']:
            evidence = json.loads((path/'evidence.json').read_text())
            for tool in evidence.get('tools', []):
                if sha(tool['path']) != tool['sha256']:
                    raise ValueError('Analysis tool changed: '+tool['name'])
                for data in tool.get('data_files', []):
                    if sha(data['path']) != data['sha256']:
                        raise ValueError('Analysis tool data changed: '+data['path'])
        for name in result.get('components', {}):
            audit_run(path/'components'/name, frozen=False)
        if 'api-diagnostics.json' in result['artifacts']:
            runtime = json.loads((path/'api-diagnostics.json').read_text())
            if sha(runtime['runtime']) != runtime['runtime_sha256']:
                raise ValueError('Scalar API runtime changed; regenerate diagnostics')
        if 'rust-tools.json' in result['artifacts']:
            from .rust import matching_model
            selected=json.loads((path/'rust-tools.json').read_text())
            for name in ['charon','aeneas']:
                if sha(selected[name]['path'])!=selected[name]['sha256']:
                    raise ValueError('Rust translation tool changed: '+name)
            if not matching_model(Path(selected['lean_lib']['path']), json.loads((path/'aeneas-model.json').read_text())):
                raise ValueError('Aeneas Lean model changed')
    return {'status':'fresh','certificate_status':result['status'],
            'qualification':'Identity/freshness audit only. Replay checks the Lean root independently.'}


def replay_run(path, output, aeneas_lean_lib=None):
    """Replay saved Lean sources without a producer, source runtime, Rust extraction or LLM."""
    path=Path(path).resolve(); audit_run(path,frozen=True)
    selection = json.loads((path/'request.json').read_text())
    if isinstance(selection, dict) and 'rust_application' in selection:
        from .application import replay as replay_application
        return replay_application(path, output, aeneas_lean_lib)
    request,source,program,questions=prepare(path/'request.json', replay=True)
    if questions: raise ValueError('Frozen request is incomplete')
    from .integration import replay_evidence
    replay_evidence(path, request, program)
    expected=kernel_for_run(path,request,program)
    if expected!=(path/'lean/Workflow/Kernel.lean').read_text():
        raise ValueError('Saved kernel/specification does not match the frozen original source/request')
    original=json.loads((path/'result.json').read_text())
    if 'lean_root_checked' not in original.get('completed_stages',[]):
        raise ValueError('This run has no checked Lean root to replay')
    if request.get('target')=='rust-aeneas':
        from .rust import model_files,tools
        if aeneas_lean_lib is not None:
            request['rust_tools']={**request.get('rust_tools',{}),'lean_lib':str(Path(aeneas_lean_lib).resolve())}
        if model_files(tools(request,proof_only=True)['lean_lib'])!=json.loads((path/'aeneas-model.json').read_text()):
            raise ValueError('Replay needs the recorded Aeneas Lean model')
    elif aeneas_lean_lib is not None:
        raise ValueError('--aeneas-lean-lib applies only to Rust-model replay')
    record=json.loads((path/'analysis.json').read_text())
    from .analysis import Bound
    bounds={n:Bound(Q(0),Q(0),Q(0),Q(record['accepted_bounds'][n])) for n in program.outputs}
    output=Path(output).resolve(); output.mkdir(parents=True,exist_ok=False)
    shutil.copytree(path/'lean',output/'lean')
    shutil.copyfile(path/'request.json',output/'request.json'); shutil.copyfile(source,output/request['source'])
    if (path/'validation.json').exists():
        shutil.copyfile(path/'validation.json', output/'validation.json')
    if (path/'model-layout.json').exists():
        shutil.copyfile(path/'model-layout.json', output/'model-layout.json')
    if (path/'c-vcs.json').exists():
        shutil.copyfile(path/'c-vcs.json', output/'c-vcs.json')
    if request.get('rust_port'):
        shutil.copyfile(path/request['rust_port']['source'], output/request['rust_port']['source'])
    runner=Runner(output,request.get('timeout_seconds',120)); work=output/'.work';work.mkdir()
    try:
        check_lean(output,request,program,bounds,runner,work,reuse=False)
    finally:
        shutil.rmtree(work)
    result={'status':'replayed', 'certificate_status':original['status'],
            'entry_theorem':'Workflow.Certificate.certificate',
            'qualification':'Fresh Lean replay only; original source-runtime diagnostics are retained in the original run.'}
    if aeneas_lean_lib is not None:
        result['aeneas_lean_lib']=request['rust_tools']['lean_lib']
    save(output/'replay.json',result)
    return result
