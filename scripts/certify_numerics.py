#!/usr/bin/env python3
"""Check numerical source models in Lean, optionally extracting Rust for checking."""
import argparse
import json
import hashlib
import sys
import tarfile

from numerics.frontend import FRONTENDS, Unsupported
from pathlib import Path
from numerics.frontend import parse
from numerics.workflow import BACKENDS, TARGETS, audit_run, certify, prepare, replay_run
from numerics.runtimes import runtime_candidates


def retain_admission_failure(args,result):
    """Preserve a CLI run's rejected admission without overwriting any run."""
    if args.command!='run':return
    output=Path(args.out).resolve()
    if output.exists():return
    try:
        raw=Path(args.request).read_bytes()
        output.mkdir(parents=True,exist_ok=False)
        (output/'original-request.json').write_bytes(raw)
        frozen=raw
        try:
            request=json.loads(raw)
            if isinstance(request,dict) and isinstance(request.get('source'),str):
                source=(Path(args.request).resolve().parent/request['source']).resolve()
                result['original_source_path']=str(source)
                if source.is_file() and source.stat().st_size<=2_000_000:
                    data=source.read_bytes();name='rejected-source'+source.suffix
                    (output/name).write_bytes(data)
                    frozen=json.dumps({**request,'source':name},indent=2).encode()+b'\n'
                    result.update(frozen_source=name,source_sha256=hashlib.sha256(data).hexdigest())
        except (ValueError,OSError) as snapshot_error:
            result['snapshot_error']=str(snapshot_error)
        (output/'request.json').write_bytes(frozen)
        (output/'admission.json').write_text(json.dumps(result,indent=2)+'\n')
        (output/'report.md').write_text('# Numerical verification: admission rejected\n\n'+
            result['error']+'\n\nNo Lean root was checked. Preserve the contract; inspect the rejected source/profile before retrying.\n')
        result['admission_report']=str(output/'report.md')
    except OSError:
        pass


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
    inspect.add_argument('--python-mixed',action='store_const',const=True,default=None,help='Admit explicit float(np.float32(x)) storage round trips')
    inspect.add_argument('--python-math',action='store_const',const=True,default=None,help='Admit explicit math.fma/math.sqrt in restricted scalar Python')
    inspect.add_argument('--python-counted',type=json.loads,help='JSON count parameter and selected iterations')
    for name in ['pack','unpack']:
        p=sub.add_parser(name)
        p.add_argument('--run' if name=='pack' else '--archive',required=True)
        p.add_argument('--out',required=True)
    recheck=sub.add_parser('recheck')
    recheck.add_argument('--run',required=True)
    recheck.add_argument('--request',required=True)
    recheck.add_argument('--out',required=True)
    recheck.add_argument('--aeneas-lean-lib')
    inspect.add_argument('--python-module',action='store_const',const=True,default=None)
    inspect.add_argument('--cpp-module',type=json.loads)
    for name in ['audit', 'replay']:
        p = sub.add_parser(name)
        p.add_argument('--run', required=True)
        if name == 'audit':
            p.add_argument('--frozen', action='store_true')
        else:
            p.add_argument('--out', required=True)
            p.add_argument('--aeneas-lean-lib', help='Relocated compiled Aeneas model; recorded hashes must match')
            p.add_argument('--timeout',type=float,help='Override only the per-command replay time limit')
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
        elif args.command in ('pack','unpack','recheck'):
            from numerics.delivery import pack,unpack,recheck
            if args.command=='pack':result=pack(args.run,args.out)
            elif args.command=='unpack':result=unpack(args.archive,args.out)
            else:result=recheck(args.run,args.request,args.out,args.aeneas_lean_lib)
        elif args.command == 'capabilities':
            from numerics.integration import adapters
            result = {'languages': list(FRONTENDS), 'backends': BACKENDS, 'targets': TARGETS,
                'adapters': {name: adapter.record() for name, adapter in adapters().items()},
                'source_profiles': {'python_module': {
                    'request_field':'python_module: true',
                    'scope':'Undecorated closed top-level scalar or scientific functions and helper closure selected from a retained full Python module',
                    'qualification':'Original definitions in isolation; module initialization, rebinding and dispatch require caller review',
                    'target':'lean-flare and Lean delivery'},
                    'cpp_module': {'request_field':'cpp_module: {constants: uppercase names to exact binary64 words}',
                    'scope':'Closed C++20 namespace-level by-value double function selected from a retained header; at most 32 straight-line operations',
                    'parser':'pycparser 3.0 is needed also for frozen replay; compiler is needed only for original diagnostics',
                    'qualification':'Selected source parsing/compiler/runtime fidelity trusted; original-header static_assert checks constants at O0/O2',
                    'excluded':'templates, objects, exceptions, memory, loops, general preprocessing and library algorithms',
                    'target':'lean-flare and Lean delivery'},
                    'python_mixed': {
                    'request_field':'python_mixed: true',
                    'runtime':'CPython 3.13/3.14 and NumPy 2.4.0; selected executable/library/platform identities retained',
                    'operations':'explicit float(np.float32(x)) storage round trips, scalar helpers and separately rounded binary64 arithmetic',
                    'arithmetic':{'format':'binary64','rounding':'nearest-even','subnormals':'gradual','fma':False,'reassociation':False,'storage':'binary32','conversion':'narrow-nearest-even-exact-widen'},
                    'limits':'32 graph nodes; one/two binary64 outputs; checked storage magnitude at most 2^126; binary32 arithmetic and unpaired casts need separate bridges',
                    'proof':'shared format/packing/rounding inference, exact widening, narrowing allowance, incoming-error propagation and independent Lean root',
                    'target':'lean with lean-flare; external producers, Rust delivery and arbitrary profile composition unsupported'},
                    'python_math': {
                    'request_field':'python_math: true',
                    'runtime':'CPython 3.13 or 3.14 with the selected math primitives; executable and math extension identities retained',
                    'operations':'import math; unshadowed math.fma(x,y,z) and math.sqrt(x), scalar helpers and ordinary separately rounded operators',
                    'arithmetic':{'format':'binary64','rounding':'nearest-even','subnormals':'gradual','fma':'explicit','reassociation':False},
                    'arithmetic_models':['separate-binary64 with correctly rounded sqrt','explicit-fma-binary64','explicit-fma-binary64 with correctly rounded sqrt'],
                    'functions':{'sqrt':'ieee754-binary64-nearest-even'},
                    'limits':'at most 32 ordered IR nodes; one or two scalar outputs; prove nonnegative native and exact radicands',
                    'proof':'native FMA/sqrt laws, checked rational root endpoints and incoming-error rules, shared enclosures, independent exact reference, numerical root and axiom audit',
                    'target':'lean with lean-flare; no external producer, Rust delivery or profile composition yet'},
                    'scientific_arrays': {
                    'request_field':'scientific_arrays: original parameter shapes; [] for scalars',
                    'languages':'Python with NumPy 2.4.0; Julia 1.11.7 ordinary typed vectors/helpers',
                    'operations':'NumPy eager elementwise + - * / with equal shapes or scalar broadcasting, zeros/array(float64), outer and read-only transpose; both languages have indexed scalar loops with fresh output mutation; Julia adds typed helpers, zeros vectors and length',
                    'limits':'NumPy rank one/two; Julia vectors; dimensions 1..8, at most 32 cells per array, 64 original cells, 1024 nodes, 10000 visited statements',
                    'reference':'independent collections algebra with Mathlib matrix products, transpose and outer',
                    'reference_normalization':'structural equality for collection graphs; extra distributive normalization limited to 32 IR nodes',
                    'integer_promotions':'Python exact bounded integers promoted to binary64 only in float64 arithmetic; integer indexing remains exact',
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
                'counterexamples': {
                    'request_field':'counterexample: {inputs: original-input hexadecimal words, output: zero-based index}',
                    'requirements':['strict_positive (positive exact reference, nonpositive native output)',
                                    'absolute_error (attained error strictly greater than unchanged output limit)'],
                    'scope':'at most 32 separate-binary64 scalar nodes; one/two finite outputs; rational references; Lean delivery',
                    'search':'counterexample_search: {tool: cbmc, output: index}; search_tools.cbmc.path selects CBMC 6.11.0; strict-positivity candidates only; ordinary Lean witness checking certifies violations',
                    'entry_theorem':'Workflow.Counterexample.counterexample',
                    'replay':'ordinary replay; no witness proposer, source execution, producer or translator'},
                'source_runtimes': {name: runtime_candidates(name) for name in FRONTENDS}}
        elif args.command == 'inspect':
            p = parse(args.language, Path(args.source).read_bytes().decode(), args.function,
                      python_arrays=args.python_arrays,
                      python_branches={'domains':'guard'} if args.guard_local else args.python_branches,
                      python_counted=args.python_counted,scientific_arrays=args.scientific_arrays,python_math=args.python_math,python_mixed=args.python_mixed,python_module=args.python_module,cpp_module=args.cpp_module)
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
            result = replay_run(args.run, args.out, args.aeneas_lean_lib,timeout_seconds=args.timeout)
        elif args.command == 'plan':
            _, _, program, questions = prepare(args.request)
            result = {'status': 'needs_input' if questions else 'ready', 'questions': questions,
                'program': program.record()}
        else:
            result = certify(args.request, args.out)
        print(json.dumps({k:v for k,v in result.items() if k not in ('dependencies','artifacts')}, indent=2))
        return 0 if result.get('status') in (None, 'ready', 'certified', 'counterexample', 'fresh', 'replayed', 'installed','bundled','unpacked','rechecked') else 2
    except RuntimeError as error:
        print(json.dumps({'status':'unresolved','error':str(error),
                          **({'failure_kind':error.kind} if hasattr(error,'kind') else {})},indent=2))
        return 2
    except (Unsupported, ValueError, KeyError, OSError, SyntaxError, ZeroDivisionError, tarfile.TarError, EOFError) as error:
        result={'status':'unsupported_or_invalid_request','error':str(error),
                'failure_kind':'unsupported_source_or_profile' if isinstance(error,Unsupported) else 'invalid_request'}
        if isinstance(error,SyntaxError):result['source_location']={'line':error.lineno,'offset':error.offset}
        retain_admission_failure(args,result)
        print(json.dumps(result,indent=2))
        return 2


if __name__ == '__main__':
    sys.exit(main())
