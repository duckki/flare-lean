"""PRECiSA candidate conclusions, including unstable-flow bounds, checked in Lean."""
from fractions import Fraction as Q
import json
from pathlib import Path
import math

from numerics.integrations.adapter_external import PINS, node_expression
from numerics.frontends.scalar import Unsupported, number
from numerics.integrations.registry import Adapter, ToolError
from numerics.analysis.enclosure import CHECKER
from numerics.analysis import scalar, checked_bounds


PIN = PINS['precisa']


def endpoint(value, lower):
    """PRECiSA parses decimal endpoints as Double, then takes toRational."""
    exact = Q(value)
    try:
        rounded = float(exact)
    except OverflowError as error:
        raise Unsupported('PRECiSA interval endpoints exceed the binary64 range') from error
    if not math.isfinite(rounded):
        raise Unsupported('PRECiSA interval endpoints must be finite binary64 values')
    if (Q.from_float(rounded) > exact if lower else Q.from_float(rounded) < exact):
        rounded = math.nextafter(rounded, -math.inf if lower else math.inf)
    if not math.isfinite(rounded):
        raise Unsupported('PRECiSA interval rounding exceeded the finite binary64 range')
    return repr(rounded)


def applicable(program, request):
    if (request.get('proof') or program.arrays or len(program.outputs) != 1 or
            len(program.nodes) > (33 if program.branches else 32)):
        raise Unsupported('PRECiSA route supports small scalar/terminal-conditional graphs')
    if any(n.op not in {'constant','neg','add','sub','mul','div','select_lt','select_le'} for n in program.nodes):
        raise Unsupported('Unsupported PRECiSA source operation')


def input_files(program, request):
    params = ','.join('a'+str(i) for i in range(len(program.inputs)))
    lines = ['analysis: THEORY', 'BEGIN', 'IMPORTING float_bounded_axiomatic@ieee754_double',
             'kernel('+params+': double): double =']
    for n in program.nodes:
        if n.op.startswith('select_'):
            a,b,t,f = n.args
            expr = 'IF '+a+(' < ' if n.op == 'select_lt' else ' <= ')+b+' THEN '+t+' ELSE '+f+' ENDIF'
        elif n.op == 'constant':
            expr = repr(number(n.bits))
        else:
            expr = node_expression(n)
        lines += ['LET '+n.name+' = '+expr+' IN']
    lines += [program.outputs[0], 'END analysis', '']
    ranges = ', '.join('a'+str(i)+' in ['+endpoint(request['domain'][name][0], True)+','+
        endpoint(request['domain'][name][1], False)+']' for i,name in enumerate(program.inputs))
    return '\n'.join(lines), 'kernel('+params+'): '+ranges+'\n'


def parse_result(text):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError('Duplicate PRECiSA JSON field: '+key)
            result[key] = value
        return result
    record = json.loads(text, object_pairs_hook=unique)
    if (not isinstance(record, dict) or set(record) != {'results','certFile','numCertFile'} or
            not isinstance(record['results'], list) or len(record['results']) != 1):
        raise ValueError('Expected one PRECiSA kernel result and certificate paths')
    if any(not isinstance(record[k], str) or not record[k].strip() for k in ('certFile','numCertFile')):
        raise ValueError('Expected PRECiSA certificate path strings')
    result = record['results'][0]
    if (not isinstance(result, dict) or set(result) != {'function','stableError','unstableError'} or
            result['function'] != 'kernel'):
        raise ValueError('Unsupported PRECiSA function/result schema')
    def bound(value):
        if type(value) not in (int, float):
            raise ValueError('Expected a finite nonnegative PRECiSA candidate')
        try:
            value = float(value)
        except OverflowError as error:
            raise ValueError('PRECiSA candidate exceeds the finite binary64 range') from error
        if not math.isfinite(value) or value < 0:
            raise ValueError('Expected a finite nonnegative PRECiSA candidate')
        # PRECiSA's JSON fields are Double upper values, encoded for round-trip.
        # Retain that binary64 value exactly, not a rounded display decimal.
        return Q.from_float(value)
    stable = bound(result['stableError'])
    unstable = None if result['unstableError'] is None else bound(result['unstableError'])
    return record, stable, unstable


def base(path, chosen):
    return Path(chosen.get('base') or path.parent.parent).expanduser().resolve()


def receipt(path, chosen):
    root = base(path, chosen)
    record = json.loads((root/'precisa-build.json').read_text())
    if not isinstance(record, dict) or not isinstance(record.get('library_sha256'), dict):
        raise ToolError('tool_identity_mismatch', 'Malformed PRECiSA build receipt')
    from numerics.workflow.certification import sha
    from numerics.integrations.setup_precisa import KODIAK, FILIB_SHA
    libraries = record['library_sha256']
    if (record.get('schema') != 'numerics-precisa-build-v1' or
            record.get('source_revision') != PIN['setup']['source']['revision'] or
            record.get('version') not in PIN['versions'] or
            record.get('kodiak_revision') != KODIAK or record.get('filib_sha256') != FILIB_SHA or
            'libkodiak.so' not in libraries or
            any(Path(name).name != name or sha(root/'lib'/name) != value for name,value in libraries.items()) or
            sha(root/'libexec/precisa') != record.get('binary_sha256')):
        raise ToolError('tool_identity_mismatch', 'PRECiSA build receipt/binary differs from the admitted source version')
    return root


def produce(session):
    chosen = session.request.get('analysis_tools', {}).get('precisa', {})
    path, env = session.tool('precisa', ['--version'], r'PRECiSA package (\S+)', PIN['versions'],
        data_files=lambda p,c: [receipt(p,c)/'precisa-build.json'],
        identity_files=lambda p,c: [receipt(p,c)/'libexec/precisa', *sorted((base(p,c)/'lib').glob('*.so*'))])
    root = session.output/'producer'
    root.mkdir()
    source, domain = input_files(session.program, session.request)
    query, ranges = root/'analysis.pvs', root/'analysis.input'
    query.write_text(source); ranges.write_text(domain)
    text = session.runner.run('precisa-analysis', [path, query, ranges, '--json', '--max-depth', '7', '--precision', '14'],
                              cwd=root, env=env, phase='analysis')
    record, stable, unstable = parse_result(text)
    for field in ('certFile','numCertFile'):
        p = Path(record[field])
        p = p if p.is_absolute() else root/p
        if not p.resolve().is_relative_to(root) or not p.is_file() or p.suffix != '.pvs':
            raise ValueError('PRECiSA certificate path is outside the producer run')
    # A null unstable field can mean the tool proved stability. The Lean check
    # still covers all four flows; that external stability claim is not assumed.
    candidate = max(stable, unstable or Q(0))
    details = {'tool':'precisa', 'evidence_form':'stable-and-unstable-error-candidates',
        'stable_candidate':str(stable), 'unstable_candidate':str(unstable) if unstable is not None else None,
        'raw_candidate_bounds':[str(candidate)], 'assume_stability':False,
        'foreign_trace_checked':False, 'source_revision':PIN['setup']['source']['revision']}
    if session.program.branches:
        from numerics.analysis.branches import proposal
    else:
        proposal = scalar.proposal
    result = proposal(session.program, session.request, [str(candidate)], details)
    return result, result.details


ADAPTERS = (Adapter('precisa','producer','stable-and-unstable-error-candidates',
    'Reconstruct PRECiSA error candidates including divergent branch choices in Lean', produce, applicable,
    {'versions':PIN['versions'], 'source_revision':PIN['setup']['source']['revision'],
     'max_arithmetic_nodes':32, 'rule_checker':CHECKER, 'fallback_rule_checker':checked_bounds.CHECKER, 'conditional_profile':'one terminal Python scalar if/else',
     'input_interpretation':'original finite binary64 inputs, exact decoded values in Lean',
     'stable_test_assumption':False, 'validation':['lean-conditional-four-flows-v1','lean-scalar-interval-v1'],
     'foreign_pvs_proof_import':False}, PIN['setup']),)
