"""Gappa proof-bearing and FPTaylor candidate output through one validation route.

Foreign traces are retained, not trusted or translated as Coq proofs. The shared
scalar validator consumes candidate conclusions and reconstructs their proofs
against the original ordered native graph.
"""
from fractions import Fraction as Q
import json
import os
from pathlib import Path
import re

from .frontend import Unsupported, number
from .integration import Adapter
from . import scalar


PINS = json.loads((Path(__file__).resolve().parents[2]/'tools/numerics/producers.json').read_text())['tools']


def applicable(program, request):
    if request.get('proof'):
        raise Unsupported('External producer routing and authored proof selection are separate routes')
    if any(node.op not in {'constant', 'neg', 'add', 'sub', 'mul', 'div'} for node in program.nodes):
        raise Unsupported('External scalar producer requires admitted arithmetic operations')
    if not scalar.supported(program):
        raise Unsupported('External scalar validation currently admits at most 32 IR nodes')


def gappa_applicable(program, request):
    applicable(program, request)
    for endpoints in request.get('domain', {}).values():
        for endpoint in endpoints:
            rational(endpoint, gappa=True)


def rational(value, gappa=False):
    value = Q(value)
    if gappa:
        if value.denominator & (value.denominator-1):
            raise Unsupported('Gappa exporter currently requires exact dyadic endpoints')
        return str(value.numerator)+'b-'+str(value.denominator.bit_length()-1)
    return '('+str(value.numerator)+'/'+str(value.denominator)+')'


def node_expression(node, ideal=False, gappa=False):
    def ref(name):
        return 'i'+name[1:] if ideal and name.startswith('n') else name
    if node.op == 'constant':
        return rational(Q.from_float(number(node.bits)), gappa)
    if node.op == 'neg':
        return '(-'+ref(node.args[0])+')'
    left, right = map(ref, node.args)
    return '('+left+{'add':'+', 'sub':'-', 'mul':'*', 'div':'/'}[node.op]+right+')'


def gappa_input(program, request, output):
    lines = ['@rnd = float<ieee_64, ne>;']
    for node in program.nodes:
        expr = node_expression(node, gappa=True)
        lines.append(node.name+' = '+(expr if node.op in ('constant', 'neg') else 'rnd('+expr+')')+';')
        lines.append('i'+node.name[1:]+' = '+node_expression(node, ideal=True, gappa=True)+';')
    domain = ' /\\ '.join('a'+str(i)+' in ['+rational(bounds[0], True)+', '+rational(bounds[1], True)+']'
                          for i, bounds in enumerate(request['domain'][name] for name in program.inputs))
    name = program.outputs[output]
    exact = 'i'+name[1:] if name.startswith('n') else name
    limit = Q(request['outputs'][output]['limit'])
    # Decimal engineering budgets need an exact enclosing dyadic query radius.
    # Query an inner radius; successful inference then implies the stated budget.
    exponent = limit.numerator.bit_length()-limit.denominator.bit_length()
    while Q(2)**exponent > limit:
        exponent -= 1
    radius = Q(2)**exponent
    lines.append('{ '+domain+' -> '+name+' - '+exact+' in ['+rational(-radius, True)+', '+rational(radius, True)+'] }')
    return '\n'.join(lines)+'\n', str(radius)


def fptaylor_input(program, request, output):
    variables = ',\n'.join('  real a'+str(i)+' in ['+rational(request['domain'][name][0])+', '+
                           rational(request['domain'][name][1])+']' for i, name in enumerate(program.inputs))
    definitions = []
    for node in program.nodes:
        operator = ' = ' if node.op in ('constant', 'neg') else ' rnd64= '
        definitions.append('  '+node.name+operator+node_expression(node))
    sections = ['Variables\n'+variables+'\n;']
    if definitions:
        sections.append('Definitions\n'+',\n'.join(definitions)+'\n;')
    sections.append('Expressions\n  '+program.outputs[output]+'\n;')
    return '\n\n'.join(sections)+'\n'


def parse_fptaylor(text):
    # Request exact hexadecimal upper values; do not round a displayed decimal
    # candidate inward. It remains untrusted until independently proved in Lean.
    values = re.findall(r'Absolute error \(exact\):?\s+[^\n]*?\((0x[0-9a-fA-F.]+p[+-]?\d+)\)', text)
    if len(values) != 1:
        raise ValueError('Expected one FPTaylor exact absolute-error hexadecimal upper value')
    try:
        result = Q.from_float(float.fromhex(values[0]))
    except (ValueError, OverflowError) as error:
        raise ValueError('Invalid finite FPTaylor error candidate') from error
    if result < 0:
        raise ValueError('Invalid negative FPTaylor error candidate')
    return str(result)


def fptaylor_base(path, chosen):
    return Path(chosen.get('base') or os.environ.get('FPTAYLOR_BASE') or path.parent).expanduser().resolve()


def produce_gappa(session):
    path, env = session.tool('gappa', ['--version'], r'Gappa (\S+)', PINS['gappa']['versions'])
    root = session.output/'producer'; root.mkdir()
    claims = []
    for index in range(len(session.program.outputs)):
        source, radius = gappa_input(session.program, session.request, index)
        query = root/f'output-{index}.g'; query.write_text(source)
        text = session.runner.run('gappa-output-'+str(index), [path, '-Bcoq', query],
                                  cwd=root, env=env, phase='analysis')
        if 'Require Import Gappa.Gappa_library.' not in text or 'Qed.' not in text:
            raise ValueError('Gappa returned no supported proof-bearing output')
        (root/f'output-{index}.v').write_text(text)
        claims.append(radius)
    details = {'tool': 'gappa', 'evidence_form': 'coq-proof-bearing-output', 'queried_error_radii': claims,
               'foreign_trace_checked': False}
    proposal = scalar.proposal(session.program, session.request, claims, details)
    return proposal, proposal.details


def produce_fptaylor(session):
    path, env = session.tool('fptaylor', ['--help'], r'FPTaylor, version (\S+)', PINS['fptaylor']['versions'],
        environment=lambda path, chosen: {'FPTAYLOR_BASE': str(fptaylor_base(path, chosen))},
        data_files=lambda path, chosen: [fptaylor_base(path, chosen)/'default.cfg'])
    root = session.output/'producer'; root.mkdir()
    candidates = []
    for index in range(len(session.program.outputs)):
        query = root/f'output-{index}.txt'
        query.write_text(fptaylor_input(session.program, session.request, index))
        text = session.runner.run('fptaylor-output-'+str(index), [path,
            '--verbosity', '0', '--abs-error', 'true', '--rel-error', 'false',
            '--print-hex-floats', 'true', '--opt', 'bb-eval', '--maxima-simplification', 'false',
            '--opt-max-iters', '1000', query], cwd=root, env=env, phase='analysis')
        candidates.append(parse_fptaylor(text))
    details = {'tool': 'fptaylor', 'evidence_form': 'numeric-candidates',
               'raw_candidate_bounds': candidates, 'foreign_trace_checked': False}
    proposal = scalar.proposal(session.program, session.request, candidates, details)
    return proposal, proposal.details


ADAPTERS = (
    Adapter('gappa', 'producer', 'coq-proof-bearing-output',
            'Reconstruct the Gappa query conclusion with reusable Lean scalar inference',
            produce_gappa, gappa_applicable,
            {'versions': PINS['gappa']['versions'], 'domain_endpoints': 'dyadic',
             'max_ir_nodes': scalar.MAX_OPERATIONS,
             'goals': ['absolute-error-budget'], 'validation': ['lean-scalar-interval-v1']},
            PINS['gappa']['setup']),
    Adapter('fptaylor', 'producer', 'numeric-candidates',
            'Validate the exact FPTaylor candidate with reusable Lean scalar inference',
            produce_fptaylor, applicable,
            {'versions': PINS['fptaylor']['versions'],
             'tested_source_revision': PINS['fptaylor']['setup']['source']['revision'],
             'max_ir_nodes': scalar.MAX_OPERATIONS,
             'goals': ['absolute-error-budget'], 'validation': ['lean-scalar-interval-v1']},
            PINS['fptaylor']['setup']),
)
