"""Closed C11 binary64 profile with explicit buffers, pure helpers and unsigned loops.

pycparser supplies syntax, not verification. Admission and the C-to-Lean mapping
are declared trust boundaries; saved replay reparses the original source.
"""
from dataclasses import replace
import importlib
import os
from pathlib import Path
import re
import sys

from .graph import Graph, Scalar, Unsupported


def parser_package():
    from .integration import ToolError
    cache=Path(os.environ.get('XDG_CACHE_HOME',Path.home()/'.cache'))/'flare'
    if sys.platform=='darwin': cache=Path.home()/'Library/Caches/flare'
    explicit=os.environ.get('FLARE_C_PARSER')
    directory=Path(explicit or cache/'pycparser-3.0')
    package=None
    if not explicit:
        try:package=importlib.import_module('pycparser')
        except ImportError:pass
        if package is not None and package.__version__ in ('3.0','3.00'):return package
    if (directory/'pycparser').is_dir():
        for name in list(sys.modules):
            if name=='pycparser' or name.startswith('pycparser.'):del sys.modules[name]
        sys.path.insert(0,str(directory));package=importlib.import_module('pycparser')
    if package is None:
        raise ToolError('missing_tool','Missing C parser: install pycparser==3.0 in the Python environment or in '+str(directory))
    if package.__version__ not in ('3.0','3.00'):
        raise ToolError('unsupported_tool_version','Unsupported pycparser version; this C profile requires 3.0')
    return package


def clean_source(source):
    if '??' in source or re.search(r'\\\r?\n',source):
        raise Unsupported('C trigraphs and line splicing are outside this profile')
    if len(source)>100000: raise Unsupported('C source exceeds the 100 KB admission limit')
    def spaces(match):return ''.join('\n' if c=='\n' else ' ' for c in match[0])
    clean=re.sub(r'/\*.*?\*/|//[^\n]*',spaces,source,flags=re.S)
    if any(c in clean for c in ['#','\\','"',"'"]) or '/*' in clean or '*/' in clean:
        raise Unsupported('C preprocessing, strings, character literals and unterminated comments are outside this profile')
    return clean


def c_frontend(source,function):
    package=parser_package(); A=importlib.import_module('pycparser.c_ast')
    try:tree=package.CParser().parse(clean_source(source),filename='source.c')
    except Exception as error:
        raise Unsupported('C syntax admission failed: '+str(error)) from error
    functions={};structs={};aliases={}
    def failure(node,message):
        raise Unsupported(message+' at '+str(getattr(node,'coord','unknown source location')))
    def type_name(node):
        if isinstance(node,A.TypeDecl): return type_name(node.type)
        if isinstance(node,A.IdentifierType): return ' '.join(node.names)
        if isinstance(node,A.Struct): return 'struct '+str(node.name)
        return None
    def structure(node):
        if not node.name or not node.decls or node.name in structs:
            failure(node,'C structs need distinct named definitions')
        fields=[]
        for field in node.decls:
            if (type_name(field.type)!='double' or not isinstance(field.type,A.TypeDecl) or
                    field.bitsize or field.init or field.quals or field.storage):
                failure(field,'C struct fields must be ordinary double values')
            fields.append(field.name)
        if len(set(fields))!=len(fields) or not 1<=len(fields)<=8:failure(node,'Unsupported C struct layout')
        structs[node.name]=fields
    for item in tree.ext:
        if isinstance(item,A.FuncDef):
            name=item.decl.name
            if name in functions:failure(item,'Duplicate C function')
            functions[name]=item
        elif isinstance(item,A.Decl) and item.name is None and isinstance(item.type,A.Struct):structure(item.type)
        elif isinstance(item,A.Typedef) and isinstance(item.type,A.TypeDecl) and isinstance(item.type.type,A.Struct):
            structure(item.type.type);aliases[item.name]=item.type.type.name
        else:failure(item,'C profile admits function definitions and named double-only structs')
    if function not in functions:raise Unsupported('Selected C function does not exist')
    def args(fn):
        decl=fn.decl
        if (not isinstance(decl.type,A.FuncDecl) or decl.storage not in ([],['static']) or
                decl.quals or decl.funcspec not in ([],['inline']) or type_name(decl.type.type) not in ('double','void')):
            failure(fn,'C functions must return double or void, with no external storage')
        result=decl.type.args.params if decl.type.args else []
        if any(not isinstance(n,A.Decl) for n in result):failure(fn,'C requires named parameters without varargs')
        return result
    selected=functions[function];api=[];names=[]
    for arg in args(selected):
        typ=arg.type
        if isinstance(typ,A.ArrayDecl):
            if (not isinstance(typ.type,A.TypeDecl) or type_name(typ.type)!='double' or
                    not isinstance(typ.dim,A.Constant) or typ.dim.type!='int' or
                    not set(typ.dim_quals)<={'restrict','static'} or 'static' not in typ.dim_quals or
                    typ.type.quals not in ([],['const'])):
                failure(arg,'C buffers need double name[static N], optional restrict and const elements')
            length=int(typ.dim.value,8 if len(typ.dim.value)>1 and typ.dim.value[0]=='0' else 10)
            if not 1<=length<=8:failure(arg,'C buffer extents must be 1..8')
            readonly='const' in typ.type.quals
            if not readonly and 'restrict' not in typ.dim_quals:
                failure(arg,'Writable C buffers require explicit restrict separation')
            inputs=[arg.name+'_'+str(i) for i in range(length)]
            api.append({'name':arg.name,'kind':'buffer','length':length,'readonly':readonly,
                        'restrict':'restrict' in typ.dim_quals,'inputs':inputs})
        elif isinstance(typ,A.TypeDecl) and not typ.quals:
            name=type_name(typ)
            if name=='double': api.append({'name':arg.name,'kind':'scalar','inputs':[arg.name]})
            elif isinstance(name,str) and ((name.startswith('struct ') and name[7:] in structs) or name in aliases):
                tag=name[7:] if name.startswith('struct ') else aliases[name]
                api.append({'name':arg.name,'kind':'struct','tag':tag,'fields':structs[tag],
                            'inputs':[arg.name+'_'+field for field in structs[tag]]})
            else:failure(arg,'C scalar parameters must be double or admitted double-only structs')
            inputs=api[-1]['inputs']
        else:failure(arg,'Pointers, casts and implicit buffer lengths need another C profile')
        names.extend(inputs)
    if len(names)>32:raise Unsupported('C profile admits at most 32 scalar input cells')
    graph=Graph('c',function,names); trace=[];loops=[];indices={};active=[]
    buffers={p['name']:p for p in api if p['kind']=='buffer'}
    cells={p['name']:[graph.names[n] for n in p['inputs']] for p in buffers.values()}
    writable=[p for p in buffers.values() if not p['readonly']]
    result_type=type_name(selected.decl.type.type)
    if (result_type=='void' and (len(writable)!=1 or writable[0]['length']>2) or
            result_type=='double' and writable):
        raise Unsupported('C void APIs update one one/two-cell buffer; double APIs have read-only buffers')
    env={p['name']:graph.names[p['name']] for p in api if p['kind']=='scalar'}
    records={p['name']:{f:graph.names[n] for f,n in zip(p['fields'],p['inputs'],strict=True)}
             for p in api if p['kind']=='struct'}
    def emit(op,*values):
        before=len(graph.nodes)
        result=graph.unary(op,values[0])
        trace.extend({'kind':'node','node':n.name} for n in graph.nodes[before:])
        return result
    def literal(node):
        if node.type=='double':
            value=float.fromhex(node.value) if node.value.lower().startswith('0x') else float(node.value)
            result=graph.literal(value);trace.append({'kind':'node','node':result.ref});return result
        if node.type=='int' and re.fullmatch(r'[0-9]+',node.value):
            value=int(node.value,8 if len(node.value)>1 and node.value[0]=='0' else 10)
            if value>2**31-1:failure(node,'C arithmetic integer literals must fit signed int; use a double literal')
            return graph.literal(value)
        failure(node,'C constants require binary64 or exactly promoted integer literals')
    def floating(value):
        before=len(graph.nodes);ref=graph.floating(value)
        trace.extend({'kind':'node','node':n.name} for n in graph.nodes[before:])
        return Scalar(ref=ref)
    def index(node):
        if isinstance(node,A.ID) and node.name in indices:return indices[node.name]
        if isinstance(node,A.Constant) and node.type in ('int','unsigned int') and re.fullmatch(r'[0-9]+[uU]?',node.value):return int(node.value.rstrip('uU'),8 if len(node.value.rstrip('uU'))>1 and node.value[0]=='0' else 10)
        if isinstance(node,A.BinaryOp) and node.op in ('+','-'):
            a,b=index(node.left),index(node.right);value=a+b if node.op=='+' else a-b
            if 0<=value<2**32:return value
        failure(node,'C buffer indices need a bounded unsigned loop index or integer constant')
    def location(node):
        if not isinstance(node,A.ArrayRef) or not isinstance(node.name,A.ID) or node.name.name not in buffers:
            failure(node,'Only direct declared buffer indexing is admitted')
        name=node.name.name;i=index(node.subscript)
        if active[-1]!=function:failure(node,'C helpers cannot capture caller buffers')
        if not 0<=i<buffers[name]['length']:failure(node,'C buffer access is out of bounds')
        return name,i
    def expr(node):
        if isinstance(node,A.ID) and node.name in env:return env[node.name]
        if isinstance(node,A.Constant):return literal(node)
        if isinstance(node,A.ArrayRef):
            name,i=location(node);value=cells[name][i]
            trace.append({'kind':'load','buffer':name,'index':i,'line':node.coord.line,'ref':graph.floating(value)})
            return value
        if isinstance(node,A.StructRef) and node.type=='.' and isinstance(node.name,A.ID) and active[-1]==function and node.name.name in records and node.field.name in records[node.name.name]:
            return records[node.name.name][node.field.name]
        if isinstance(node,A.BinaryOp) and node.op in ('+','-','*','/'):
            left,right=expr(node.left),expr(node.right)
            # Integer promotions emit nodes too; retain their exact graph order.
            before=len(graph.nodes);value=graph.binary({'+':'add','-':'sub','*':'mul','/':'div'}[node.op],left,right)
            trace.extend({'kind':'node','node':n.name} for n in graph.nodes[before:]);return value
        if isinstance(node,A.UnaryOp) and node.op in ('+','-'):
            return emit('neg' if node.op=='-' else 'pos',expr(node.expr))
        if isinstance(node,A.FuncCall) and isinstance(node.name,A.ID) and node.name.name in functions and node.name.name not in env and node.name.name not in indices and node.name.name not in buffers and node.name.name not in records:
            values=[expr(n) for n in (node.args.exprs if node.args else [])]
            return call(node.name.name,values)
        failure(node,'Unsupported C numeric expression '+type(node).__name__)
    work=0
    def body(node,in_loop=False):
        nonlocal work
        statements=node.block_items if isinstance(node,A.Compound) else [node]
        returned=None
        for statement in statements or []:
            work+=1
            if work>2000 or len(graph.nodes)>512:failure(statement,'C source exceeds the bounded work limit')
            if returned is not None:failure(statement,'C statements after return are unsupported')
            if isinstance(statement,A.Decl):
                if (not isinstance(statement.type,A.TypeDecl) or type_name(statement.type)!='double' or
                        statement.quals or statement.storage or statement.name in env or statement.name in buffers or
                        statement.name in indices or statement.init is None):
                    failure(statement,'C locals must be fresh initialized double values')
                value=expr(statement.init)
                env[statement.name]=floating(value)
            elif isinstance(statement,A.Assignment) and statement.op=='=':
                value=expr(statement.rvalue)
                value=floating(value)
                target=statement.lvalue
                if isinstance(target,A.ID) and target.name in env:env[target.name]=value
                elif isinstance(target,A.ArrayRef):
                    name,i=location(target)
                    if buffers[name]['readonly']:failure(target,'C must not write a const input buffer')
                    cells[name][i]=value;trace.append({'kind':'store','buffer':name,'index':i,'line':target.coord.line,'ref':value.ref})
                else:failure(target,'C assignment needs a scalar local or writable buffer cell')
            elif isinstance(statement,A.For):
                declarations=statement.init.decls if isinstance(statement.init,A.DeclList) else []
                if len(declarations)!=1:failure(statement,'C loop requires one unsigned initializer')
                decl=declarations[0];name=decl.name;condition=statement.cond;increment=statement.next
                if (decl.quals or decl.storage or type_name(decl.type)!='unsigned int' or not isinstance(decl.init,A.Constant) or decl.init.value!='0' or
                    name in env or name in buffers or name in indices or
                    not isinstance(condition,A.BinaryOp) or condition.op!='<' or not isinstance(condition.left,A.ID) or condition.left.name!=name or
                    not isinstance(condition.right,A.Constant) or condition.right.type not in ('int','unsigned int') or
                    not isinstance(increment,A.UnaryOp) or increment.op not in ('++','p++') or not isinstance(increment.expr,A.ID) or increment.expr.name!=name):
                    failure(statement,'C loops require for (unsigned int i=0; i<N; ++i)')
                count=index(condition.right)
                if not 1<=count<=128:failure(statement,'C counted loop must have 1..128 iterations')
                loops.append({'line':statement.coord.line,'counter':name,'iterations':count,'width':32})
                for i in range(count):
                    indices[name]=i;before=set(env);body(statement.stmt,True)
                    for key in set(env)-before:del env[key]
                del indices[name]
            elif isinstance(statement,A.Return) and not in_loop:
                returned=expr(statement.expr) if statement.expr is not None else False
            else:failure(statement,'Unsupported C statement '+type(statement).__name__)
        return returned
    def call(name,values):
        nonlocal env,records
        if name in active or len(active)>=16:raise Unsupported('Recursive C helpers are outside this profile')
        fn=functions[name];parameters=args(fn)
        if name!=function and (type_name(fn.decl.type.type)!='double' or any(type_name(p.type)!='double' or not isinstance(p.type,A.TypeDecl) or p.quals for p in parameters)):
            failure(fn,'C numerical helpers take and return scalar doubles')
        if len(parameters)!=len(values):failure(fn,'C helper arity mismatch')
        saved=env;env=dict(zip((p.name for p in parameters),(floating(v) for v in values),strict=True));active.append(name)
        try:
            value=body(fn.body)
            if not isinstance(value,Scalar):failure(fn,'C helper requires a scalar double return')
            return floating(value)
        finally:env=saved;active.pop()
    # The selected API may also expose buffers/struct values, so execute its body
    # in the explicitly initialized environment rather than helper parameter binding.
    active.append(function);result=body(selected.body);active.pop()
    if result_type=='double':
        if not isinstance(result,Scalar):failure(selected,'C double API requires a scalar return')
        outputs=[floating(result)]
    else:
        if result not in (None,False):failure(selected,'C void API must not return a value')
        outputs=cells[writable[0]['name']]
    program=graph.finish(outputs)
    if len(program.nodes)>512:raise Unsupported('C source exceeds the 512-node limit')
    return replace(program,c={'schema':'c-binary64-buffers-v1','parser':'pycparser-3.0',
        'api':api,'return_type':result_type,'trace':trace,'loops':loops,'structs':structs,
        'writable':writable[0]['name'] if writable else None})
