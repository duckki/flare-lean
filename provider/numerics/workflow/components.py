"""Certified numerical components imported into an application proof namespace."""
import json
from pathlib import Path
import re


def validate(selection, base, *, replay=False):
    from numerics.workflow.certification import prepare
    if not isinstance(selection, dict):
        raise ValueError('Application components must map names to request paths')
    for name, source in selection.items():
        if not isinstance(name, str) or not re.fullmatch(r'[A-Z][A-Za-z_0-9]*', name):
            raise ValueError('Component names must be Lean namespace identifiers beginning with a capital')
        if not isinstance(source, str):
            raise ValueError('Component selection must name a request file')
        path = (base/source).resolve()
        raw = json.loads(path.read_text())
        if not isinstance(raw, dict) or 'rust_application' in raw or raw.get('target', 'lean') != 'lean':
            raise ValueError('Application components must be independent Lean numerical requests')
        _, _, _, questions = prepare(path, replay=replay)
        if questions:
            raise ValueError('Incomplete numerical component: '+name)


def sources(run, name):
    """Relocate closed proof modules, preserving every namespace reference."""
    prefix = 'Workflow.Components.'+name
    result = {}
    for path in sorted((run/'lean/Workflow').rglob('*.lean')):
        if path.name == 'Check.lean':
            continue
        relative = path.relative_to(run/'lean/Workflow')
        text = re.sub(r'\bWorkflow\b', prefix, path.read_text())
        result[Path('Workflow/Components')/name/relative] = text
    return result


def materialize(output, selection):
    """Reconstruct component imports from sealed producer evidence, also on replay."""
    from numerics.workflow.certification import audit_run, prepare, sha
    descriptions = {}
    for name in selection:
        run = output/'components'/name
        audit_run(run, frozen=True)
        record = json.loads((run/'result.json').read_text())
        if record['status'] != 'certified' or 'lean_root_checked' not in record['completed_stages']:
            raise ValueError('Numerical component has no accepted in-budget Lean root: '+name)
        request, source, program, questions = prepare(run/'request.json', replay=True)
        if questions:
            raise ValueError('Frozen numerical component is incomplete')
        from numerics.workflow.certification import kernel_for_run
        if kernel_for_run(run, request, program) != (run/'lean/Workflow/Kernel.lean').read_text():
            raise ValueError('Component kernel differs from its original source: '+name)
        for relative, text in sources(run, name).items():
            path = output/'lean'/relative
            if path.exists() and path.read_text() != text:
                raise ValueError('Imported component source changed: '+str(relative))
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        descriptions[name] = {'source_sha256': sha(source), 'outputs': record['outputs'],
                              'entry': 'Workflow.Components.'+name+'.Certificate.certificate'}
    return descriptions


def generate(base, output, selection):
    from numerics.workflow.certification import certify, save
    for name, request in selection.items():
        run = output/'components'/name
        result = certify((base/request).resolve(), run)
        if result.get('status') != 'certified':
            raise ValueError('Numerical component failed certification: '+name+' ('+result['status']+')')
    descriptions = materialize(output, selection)
    save(output/'components.json', descriptions)
    return descriptions
