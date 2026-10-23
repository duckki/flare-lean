"""Existing producer and Rust extractor exposed through the common adapter API."""
from .integration import Adapter, Proposal


def produce(session):
    summaries, steps = session.baseline(session.program, session.request)
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
