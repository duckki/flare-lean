#!/usr/bin/env python3
"""Check numerical source models in Lean, optionally extracting Rust for checking."""
import argparse
import json
import sys

from numerics.frontend import FRONTENDS, Unsupported
from pathlib import Path
from numerics.frontend import parse
from numerics.workflow import BACKENDS, TARGETS, audit_run, certify, prepare, replay_run
from numerics.runtimes import runtime_candidates


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    sub.add_parser('capabilities')
    setup = sub.add_parser('setup')
    setup.add_argument('--tool', required=True)
    setup.add_argument('--out', required=True, type=Path)
    setup.add_argument('--timeout', type=float, default=600)
    setup.add_argument('--make-arg', action='append', default=[])
    inspect = sub.add_parser('inspect')
    inspect.add_argument('--source', required=True)
    inspect.add_argument('--function', required=True)
    inspect.add_argument('--language', default='python')
    inspect.add_argument('--python-arrays', type=json.loads, help='JSON mapping input names to fixed list shapes')
    inspect.add_argument('--python-branches', action='store_const', const=True, default=None,
                         help='Admit one terminal scalar Python if/else')
    for name in ['audit', 'replay']:
        p = sub.add_parser(name)
        p.add_argument('--run', required=True)
        if name == 'audit':
            p.add_argument('--frozen', action='store_true')
        else:
            p.add_argument('--out', required=True)
            p.add_argument('--aeneas-lean-lib', help='Relocated compiled Aeneas model; recorded hashes must match')
    for name in ['plan', 'run']:
        p = sub.add_parser(name)
        p.add_argument('--request', required=True)
        if name == 'run':
            p.add_argument('--out', required=True)
    args = parser.parse_args()
    try:
        if args.command == 'setup':
            from numerics.installation import setup
            result = setup(args.tool, args.out, args.timeout, args.make_arg)
        elif args.command == 'capabilities':
            from numerics.integration import adapters
            result = {'languages': list(FRONTENDS), 'backends': BACKENDS, 'targets': TARGETS,
                'adapters': {name: adapter.record() for name, adapter in adapters().items()},
                'source_profiles': {'rust_application': {
                    'request_field': 'rust_application',
                    'inputs': 'dependency-free multi-module Rust crate; original public API',
                    'contract': 'reviewed Workflow.Contract.Statement applied to the fresh extracted entry',
                    'proof': 'authored Lean modules; root type and transitive axioms checked independently',
                    'components': 'independent closed numerical requests imported into namespaced application proofs',
                    'source_api': 'ordinary Python scalar constructor/full-state update, options and nonzero-divisor scope',
                    'target': 'rust-aeneas; translator support and explicit semantic bridges required'},
                    'python_branches': {'request_field':'python_branches: true',
                    'inputs':'one ordinary scalar Python function; at most 32 arithmetic nodes',
                    'operations':'scalar assignments, one terminal if/else, one ordered comparison, scalar returns',
                    'proof':'all four native/exact branch choices; no stable-test assumption',
                    'target':'lean with lean-flare or precisa; both arms must satisfy numerical premises'},
                    'python_arrays': {'request_field':'python_arrays',
                    'inputs':'two built-in list operands: rank-two left matrix, rank-one/two right operand',
                    'dimensions':'1 through 8; at most 32 output entries',
                    'operations':'fixed indexing, fresh scalar updates, shape assertions, local helpers, range(size), ascending separately rounded products',
                    'target':'lean; no NumPy/BLAS bridge or automatic array Rust port'}},
                'source_runtimes': {name: runtime_candidates(name) for name in FRONTENDS}}
        elif args.command == 'inspect':
            p = parse(args.language, Path(args.source).read_text(), args.function,
                      python_arrays=args.python_arrays, python_branches=args.python_branches)
            result = {'status': 'needs_input', 'program': p.record(), 'required_inputs': {
                'domain': {name: '[lower, upper] as exact rational strings' for name in p.inputs},
                'outputs': [{'name': '', 'unit': '', 'limit': ''} for _ in p.outputs],
                'specification': {'kind':'matrix','expression':'independent matrix expression over original array names'} if p.arrays else
                    ['independent exact expression over input names' for _ in p.outputs]}}
        elif args.command == 'audit':
            result = audit_run(args.run, args.frozen)
        elif args.command == 'replay':
            result = replay_run(args.run, args.out, args.aeneas_lean_lib)
        elif args.command == 'plan':
            _, _, program, questions = prepare(args.request)
            result = {'status': 'needs_input' if questions else 'ready', 'questions': questions,
                'program': program.record()}
        else:
            result = certify(args.request, args.out)
        print(json.dumps({k:v for k,v in result.items() if k not in ('dependencies','artifacts')}, indent=2))
        return 0 if result.get('status') in (None, 'ready', 'certified', 'fresh', 'replayed', 'installed') else 2
    except RuntimeError as error:
        print(json.dumps({'status':'unresolved','error':str(error)},indent=2))
        return 2
    except (Unsupported, ValueError, KeyError, OSError, SyntaxError, ZeroDivisionError) as error:
        print(json.dumps({'status': 'unsupported_or_invalid_request', 'error': str(error)}, indent=2))
        return 2


if __name__ == '__main__':
    sys.exit(main())
