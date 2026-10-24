"""Versioned tool roles, shared admission and evidence tied to a frozen obligation.

Adapters produce untrusted proposals. The existing independent Lean root check
remains the certification boundary; a foreign proof is not imported implicitly.
"""
from dataclasses import dataclass, field, replace
from fractions import Fraction as Q
import hashlib
import importlib
import json
import os
from pathlib import Path
import re
import shutil

from .frontend import Unsupported


ARITHMETIC = {
    'format': 'binary64', 'rounding': 'nearest-even', 'subnormals': 'gradual',
    'fma': False, 'reassociation': False,
}


EXPLICIT_FMA_ARITHMETIC = {**ARITHMETIC, 'fma':'explicit'}


def arithmetic(program):
    operations = program.math['operations'] if program.math else []
    model = EXPLICIT_FMA_ARITHMETIC if 'fma' in operations else ARITHMETIC
    if 'sqrt' in operations:
        return {**model,'functions':{'sqrt':'ieee754-binary64-nearest-even'}}
    return model


def digest(record):
    return hashlib.sha256(json.dumps(record, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


@dataclass(frozen=True)
class Adapter:
    name: str
    role: str
    evidence: str
    description: str
    execute: object
    applicable: object = lambda program, request: None
    constraints: dict = field(default_factory=dict)
    setup: dict | None = None

    def record(self):
        return {'schema': 'numerics-capability-v1', 'name': self.name, 'role': self.role,
                'evidence': self.evidence, 'description': self.description,
                'arithmetic': dict(ARITHMETIC), 'constraints': self.constraints,
                'setup': self.setup}


def adapters():
    """New provider adapters register from their own module, without workflow edits."""
    registry = {}
    for path in sorted(Path(__file__).parent.glob('adapter_*.py')):
        module = importlib.import_module('.'+path.stem, __package__)
        for adapter in module.ADAPTERS:
            if adapter.name in registry:
                raise ValueError('Duplicate tool adapter: '+adapter.name)
            registry[adapter.name] = adapter
    return registry


def select(name, role, program, request):
    adapter = adapters().get(name)
    if adapter is None or adapter.role != role:
        raise Unsupported('No admitted '+role+' adapter: '+name)
    adapter.applicable(program, request)
    return adapter


def validate(request, program, require_adapters=True):
    expected = arithmetic(program)
    model = request.get('arithmetic', expected)
    if model != expected or any(type(model[key]) is not type(value) for key, value in expected.items()):
        fusion = ('explicit FMA' if expected['fma'] else 'separate operations with FMA disabled')
        if 'functions' in expected:
            fusion += ' and the declared binary64 square-root contract'
        raise Unsupported('Unsupported arithmetic model; require nearest/even binary64 with gradual underflow and '+fusion)
    producer = request.get('producer', 'lean-flare')
    if not isinstance(producer, str):
        raise ValueError('producer must name an adapter')
    if require_adapters:
        select(producer, 'producer', program, request)
    if require_adapters and request.get('target') == 'rust-aeneas':
        select('rust-aeneas', 'extractor', program, request)
    tools = request.get('analysis_tools', {})
    if not isinstance(tools, dict):
        raise ValueError('analysis_tools must map adapter names to tool selections')
    for name, selection in tools.items():
        if (require_adapters and name not in adapters()) or not isinstance(selection, dict):
            raise ValueError('Unknown analysis tool selection: '+name)
        if set(selection)-{'executable', 'sha256', 'base'}:
            raise ValueError('Tool selection supports executable, sha256 and base')
        for key, value in selection.items():
            if not isinstance(value, str) or not value.strip():
                raise ValueError('Tool selection fields must be nonempty strings')
            if key == 'sha256' and not re.fullmatch('[0-9a-f]{64}', value):
                raise ValueError('Expected lowercase SHA-256 tool identity')


def obligation(program, request, source_sha256):
    return {'schema': 'numerics-obligation-v1', 'source_sha256': source_sha256,
            'program': json.loads(json.dumps(program.record())), 'domain': request['domain'],
            'specification': request['specification'], 'outputs': request['outputs'],
            'arithmetic': dict(arithmetic(program))}


@dataclass
class Proposal:
    summaries: dict
    steps: list
    claims: dict
    details: dict = field(default_factory=dict)
    lean_source: str | None = None
    authored: dict | None = None
    modules: dict = field(default_factory=dict)
    layout: list | None = None


class Session:
    def __init__(self, program, request, output, work, runner, baseline, source_name):
        from .workflow import save, sha
        self.program, self.request = program, request
        self.output, self.work, self.runner, self.baseline = output, work, runner, baseline
        self.source_name = source_name
        frozen = obligation(program, request, sha(output/source_name))
        self.obligation = frozen
        self.identity = digest(frozen)
        self.evidence = {'schema': 'numerics-evidence-v1', 'obligation_sha256': self.identity,
                         'selected_producer': request.get('producer', 'lean-flare'), 'records': []}
        save(output/'obligation.json', frozen)
        self.save()

    def save(self):
        from .workflow import save
        save(self.output/'evidence.json', self.evidence)

    def record(self, adapter, details):
        self.evidence['records'].append({**adapter.record(), 'arithmetic':dict(arithmetic(self.program)), 'details': details})
        self.save()

    def execute(self, name, role, **arguments):
        adapter = select(name, role, self.program, self.request)
        value, details = adapter.execute(self, **arguments)
        if role == 'producer':
            from .analysis import Bound
            if (not isinstance(value, Proposal) or set(value.claims) != set(self.program.outputs) or
                    any(not isinstance(bound, Bound) or any(not isinstance(x, Q) for x in
                        [bound.c, bound.w, bound.i, bound.e]) for bound in value.claims.values())):
                raise ValueError('Malformed producer proposal or output claims')
        self.record(adapter, details)
        return value

    def tool(self, name, version_args, version_pattern, versions, environment=None, data_files=None, identity_files=None):
        """Resolve existing/user-installed tools with common identity and version checks."""
        from .workflow import sha
        self.runner.last_stage = name+'-admission'
        chosen = self.request.get('analysis_tools', {}).get(name, {})
        configured = chosen.get('executable') or os.environ.get('FLARE_'+name.upper()) or name
        executable = shutil.which(os.path.expanduser(configured))
        if not executable:
            raise ToolError('missing_tool', 'Missing analysis tool '+name+'; install a supported version or set FLARE_'+name.upper())
        path = Path(executable).absolute()
        actual = sha(path)
        if chosen.get('sha256', actual) != actual:
            raise ToolError('tool_identity_mismatch', 'Analysis tool identity changed: '+name)
        environment = environment(path, chosen) if environment else {}
        text = self.runner.run(name+'-version', [path, *version_args], env=environment, phase='admission')
        match = re.search(version_pattern, text)
        if match is None or match[1] not in versions:
            raise ToolError('unsupported_tool_version', 'Unsupported '+name+' version; supported: '+', '.join(versions))
        record = {'name': name, 'path': str(path), 'sha256': actual, 'version': match[1],
                  'environment': environment}
        for index, data in enumerate(data_files(path, chosen) if data_files else []):
            data = Path(data).resolve()
            if not data.is_file():
                raise ToolError('missing_tool_data', 'Missing '+name+' tool data: '+str(data))
            snapshot = self.output/'tool-data'/name/(str(index)+'-'+data.name)
            snapshot.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(data, snapshot)
            record.setdefault('data_files', []).append({'path': str(data), 'sha256': sha(snapshot),
                                                       'snapshot': str(snapshot.relative_to(self.output))})
        for data in identity_files(path, chosen) if identity_files else []:
            data = Path(data).resolve()
            if not data.is_file():
                raise ToolError('missing_tool_data', 'Missing '+name+' identity file: '+str(data))
            record.setdefault('data_files', []).append({'path': str(data), 'sha256': sha(data)})
        self.evidence.setdefault('tools', []).append(record)
        self.save()
        return path, environment

    def budget_proposal(self, details):
        """Independently derive the requested bound; sharper tool output stays a candidate."""
        self.runner.last_stage = 'analysis'
        summaries, steps = self.baseline(self.program, self.request)
        claims = {name: replace(summaries[name], e=Q(target['limit']))
                  for name, target in zip(self.program.outputs, self.request['outputs'], strict=True)}
        return Proposal(summaries, steps, claims, {
            **details, 'validation': 'independent-lean-rederivation-v1',
            'claim_policy': 'requested-budgets',
            'qualification': 'Raw foreign output is retained as untrusted evidence. Lean independently checks the requested budgets; sharper printed candidates are not certified.'})

    def proof_module(self, proposal):
        """Freeze an adapter-generated Lean argument for the existing typed root check."""
        from .workflow import save
        if proposal.lean_source is None:
            if proposal.authored is not None:
                raise ValueError('Adapter proof metadata needs its generated Lean source')
            return self.request.get('proof')
        metadata = proposal.authored
        if (self.request.get('proof') or not isinstance(proposal.lean_source, str) or
                not isinstance(metadata, dict) or set(metadata)-{'accuracy', 'specification_equiv'} or
                'accuracy' not in metadata or any(not isinstance(value, str) or not re.fullmatch(
                    r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', value)
                    for value in metadata.values())):
            raise ValueError('Adapter Lean argument needs source text and valid accuracy/specification declarations')
        path = self.output/'lean/Workflow/Authored.lean'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(proposal.lean_source)
        for name, source in proposal.modules.items():
            if (not isinstance(name, str) or not re.fullmatch(r'Workflow/(?:[A-Za-z_][A-Za-z_0-9]*/)*[A-Za-z_][A-Za-z_0-9]*\.lean', name)
                    or name in {'Workflow/Authored.lean','Workflow/Kernel.lean','Workflow/Proof.lean','Workflow/Check.lean'}
                    or not isinstance(source, str)):
                raise ValueError('Invalid adapter proof module')
            target = self.output/'lean'/name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(source)
        if proposal.layout is not None:
            from .composition import groups
            expected = groups(self.program, (self.output/self.source_name).read_text(), self.request)
            if proposal.layout != expected:
                raise ValueError('Composed model does not match original source helper boundaries')
            save(self.output/'model-layout.json', {'schema':'numerics-helper-layout-v1', 'calls':proposal.layout})
        save(self.output/'validation.json', {'schema': 'numerics-validation-v1',
             'kind': 'adapter-lean-module', 'declarations': metadata,
             **({'modules': list(proposal.modules)} if proposal.modules else {})})
        return metadata


def replay_evidence(path, request, program):
    """Bind replay to the frozen obligation; never rerun producer admission or setup."""
    from .workflow import sha
    evidence_path = path/'evidence.json'
    if not evidence_path.exists():
        return  # Pre-interface certificates retain their original replay path.
    actual = json.loads((path/'obligation.json').read_text())
    expected = obligation(program, request, sha(path/request['source']))
    evidence = json.loads(evidence_path.read_text())
    if digest(actual) != digest(expected) or evidence.get('schema') != 'numerics-evidence-v1' or evidence.get('obligation_sha256') != digest(expected):
        raise ValueError('Tool evidence does not match the frozen source/domain/reference/arithmetic obligation')
    producer = request.get('producer', 'lean-flare')
    if evidence.get('selected_producer') != producer or not any(
            record.get('name') == producer and record.get('role') == 'producer'
            for record in evidence.get('records', [])):
        raise ValueError('Selected producer does not match the frozen evidence records')


class ToolError(RuntimeError):
    def __init__(self, kind, message):
        super().__init__(message)
        self.kind = kind
