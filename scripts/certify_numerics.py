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
    inspect.add_argument('--scientific-arrays', type=json.loads, help='JSON original parameter shapes for closed NumPy/Julia arrays; [] for scalars')
    inspect.add_argument('--python-arrays', type=json.loads, help='JSON mapping input names to fixed list shapes')
    inspect.add_argument('--python-branches', action='store_const', const=True, default=None,
                         help='Admit one terminal scalar Python if/else')
    inspect.add_argument('--guard-local',action='store_true',help='Prove arithmetic only on the direct input guard domain')
    inspect.add_argument('--python-math',action='store_const',const=True,default=None,help='Admit explicit math.fma in restricted scalar Python')
    inspect.add_argument('--python-counted',type=json.loads,help='JSON count parameter and selected iterations')
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
                'source_profiles': {'python_math': {
                    'request_field':'python_math: true',
                    'runtime':'CPython 3.13 or 3.14 with math.fma; executable and math extension identities retained',
                    'operations':'import math; unshadowed math.fma(x,y,z), scalar helpers and ordinary separately rounded operators',
                    'arithmetic':{'format':'binary64','rounding':'nearest-even','subnormals':'gradual','fma':'explicit','reassociation':False},
                    'limits':'at most 32 ordered IR nodes; one or two scalar outputs',
                    'proof':'native single-rounding FMA law, shared rational enclosure rules, independent exact reference, numerical root and axiom audit',
                    'target':'lean with lean-flare; no external producer, Rust delivery or profile composition yet'},
                    'scientific_arrays': {
                    'request_field':'scientific_arrays: original parameter shapes; [] for scalars',
                    'languages':'Python with NumPy 2.4.0; Julia 1.11.7 ordinary typed vectors/helpers',
                    'operations':'NumPy eager elementwise + - * / with equal shapes or scalar broadcasting, zeros/array(float64), outer and read-only transpose; both languages have indexed scalar loops with fresh output mutation; Julia adds typed helpers, zeros vectors and length',
                    'limits':'NumPy rank one/two; Julia vectors; dimensions 1..8, at most 32 cells per array, 64 original cells, 1024 nodes, 10000 visited statements',
                    'reference':'independent collections algebra with Mathlib matrix products, transpose and outer',
                    'proof':'typed tensor dimensions/data sizes, source model execution, explicit access conditions, finiteness, accuracy and budgets in one Lean root',
                    'target':'lean; retained fixed-array/scalar Rust APIs with at most two output cells and authored fresh-extraction bridges',
                    'excluded':'BLAS/matmul/dot, NumPy reductions, arbitrary broadcasting, dtype changes, views/input mutation, fused Julia broadcast and general library dispatch'},
                    'c': {
                    'parser':'pycparser 3.0; optional dependency, also needed for frozen-source replay',
                    'inputs':'closed C11 double functions, pure scalar helpers, double-only value structs and static buffers',
                    'operations':'separate binary64 arithmetic; unsigned int loops with constant bounds 1..128; no casts, preprocessing, allocation, pointer escape or indirect calls',
                    'limits':'32 scalar input cells, 512 graph nodes, buffer extents 1..8; void APIs update one one/two-cell restrict buffer',
                    'proof':'source access/counter conditions and numerical allowances in one Lean root; buffer roots include region validity, separation, execution and unchanged cells',
                    'target':'lean for buffers; scalar/value-struct APIs also support retained Rust ports with checked correspondence proofs'},
                    'rust_application': {
                    'request_field': 'rust_application',
                    'inputs': 'dependency-free multi-module Rust crate; original public API',
                    'contract': 'reviewed Workflow.Contract.Statement applied to the fresh extracted entry',
                    'proof': 'authored Lean modules; root type and transitive axioms checked independently',
                    'components': 'independent closed numerical requests imported into namespaced application proofs',
                    'source_api': 'ordinary Python scalar constructor/full-state update, options and nonzero-divisor scope',
                    'target': 'rust-aeneas; translator support and explicit semantic bridges required'},
                    'python_counted': {'request_field':'python_counted',
                    'inputs':'ordinary Python two-state range(count) loop; selected nonnegative integer count',
                    'operations':'one scalar helper call per iteration; at most 64 helper nodes; fixed float configuration',
                    'proof':'one initialized/preserved native/exact invariant for all natural horizons; selected count instantiated at root',
                    'target':'lean with lean-flare; no stream indexing or automatic Rust loop port'},
                    'python_branches': {'request_field':'python_branches: true or {"domains":"guard"}',
                    'inputs':'one ordinary scalar Python function; at most 32 arithmetic nodes',
                    'operations':'scalar assignments, one terminal if/else, one ordered comparison, scalar returns',
                    'proof':'true profile checks all four native/exact choices; guard-local profile proves direct guard agreement and local premises',
                    'target':'lean; default checks both arms with lean-flare/precisa; guard domains use lean-flare and a direct input/literal comparison'},
                    'python_arrays': {'request_field':'python_arrays',
                    'inputs':'two built-in list operands: rank-two left matrix, rank-one/two right operand',
                    'dimensions':'1 through 8; at most 32 output entries',
                    'operations':'fixed indexing, fresh scalar updates, shape assertions, local helpers, range(size), ascending separately rounded products',
                    'target':'lean; no NumPy/BLAS bridge or automatic array Rust port'}},
                'source_runtimes': {name: runtime_candidates(name) for name in FRONTENDS}}
        elif args.command == 'inspect':
            p = parse(args.language, Path(args.source).read_text(), args.function,
                      python_arrays=args.python_arrays,
                      python_branches={'domains':'guard'} if args.guard_local else args.python_branches,
                      python_counted=args.python_counted,scientific_arrays=args.scientific_arrays,python_math=args.python_math)
            result = {'status': 'needs_input', 'program': p.record(), 'required_inputs': {
                'domain': {name: '[lower, upper] as exact rational strings' for name in p.inputs},
                'outputs': [{'name': '', 'unit': '', 'limit': ''} for _ in p.outputs],
                'specification': {'kind':'collections','bindings':[],'outputs':['independent exact collection expression' for _ in p.scientific['outputs']]} if p.scientific else
                    {'kind':'iterate','initial':['',''],'state':['state0','state1'],'step':['','']} if p.counted else
                    {'kind':'matrix','expression':'independent matrix expression over original array names'} if p.arrays else
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
        print(json.dumps({'status':'unresolved','error':str(error),
                          **({'failure_kind':error.kind} if hasattr(error,'kind') else {})},indent=2))
        return 2
    except (Unsupported, ValueError, KeyError, OSError, SyntaxError, ZeroDivisionError) as error:
        print(json.dumps({'status': 'unsupported_or_invalid_request', 'error': str(error)}, indent=2))
        return 2


if __name__ == '__main__':
    sys.exit(main())
