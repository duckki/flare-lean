"""Existing producer and Rust extractor exposed through the common adapter API."""
from .integration import Adapter, Proposal


def produce(session):
    from . import scalar
    from . import composition
    from fractions import Fraction as Q
    if session.program.branches:
        from .branches import proposal
        value = proposal(session.program, session.request)
        return value, value.details
    if session.program.arrays:
        from .analysis import analyze, scale_normalized
        summaries,steps=analyze(session.program,session.request['domain'],scale_normalized)
        details={'validation':'lean-ordered-array-product-v1',
                 'qualification':'Fixed shapes and the original ascending product schedule; numerical premises and the array root are checked in Lean.'}
        return Proposal(summaries,steps,{name:summaries[name] for name in session.program.outputs},details),details
    if not session.program.arrays and not session.request.get('proof') and isinstance(session.request.get('specification'), dict):
        source = (session.output/session.source_name).read_text()
        calls = composition.groups(session.program, source, session.request)
        if calls:
            value = composition.proposal(session.program, session.request, calls)
            return value, value.details
    try:
        summaries, steps = session.baseline(session.program, session.request)
    except ValueError:
        if session.request.get('proof') or not scalar.supported(session.program):
            raise
        value = scalar.proposal(session.program, session.request)
        return value, value.details
    if (not session.request.get('proof') and scalar.supported(session.program) and
            any(summaries[name].e > Q(target['limit']) for name,target in
                zip(session.program.outputs, session.request['outputs'], strict=True))):
        value = scalar.proposal(session.program, session.request)
        return value, value.details
    claims = {name: summaries[name] for name in session.program.outputs}
    details = {'validation': 'lean-flare-v1', 'proof_source': bool(session.request.get('proof')),
               'qualification': 'Untrusted proposals; the independent Lean root checks all accepted numerical claims.'}
    return Proposal(summaries, steps, claims, details), details


def extract(session, source):
    from .rust import extract as extract_rust
    extract_rust(session.program, source, session.request, session.output, session.work, session.runner)
    return None, {'model': 'aeneas-model.json', 'tools': 'rust-tools.json',
                  'validation': 'extracted-return-in-lean-root',
                  'qualification': 'Charon/Aeneas translation and model remain declared source-model trust boundaries.'}


def check(session, bounds):
    from .workflow import check_lean
    check_lean(session.output, session.request, session.program, bounds, session.runner, session.work)
    return None, {'entry_theorem': 'Workflow.Certificate.certificate',
                  'validation': 'independent-root-type-and-transitive-axioms'}


ADAPTERS = (
    Adapter('lean-flare', 'producer', 'rational-proposals-or-authored-lean',
            'Existing FLARE compositional numerical proof generation', produce),
    Adapter('rust-aeneas', 'extractor', 'lean-source-model',
            'Fresh Charon/Aeneas extraction with the actual return relation checked in Lean', extract),
    Adapter('lean-root', 'validator', 'lean-proof-terms',
            'Compile proof modules and independently check the root type and its axioms', check),
)
