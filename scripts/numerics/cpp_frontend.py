"""Closed by-value C++20 double functions selected from ordinary headers.

Only built-in scalar arithmetic is lowered through the existing C syntax bridge.
Configured external constants are exact words, checked by compiler static_assert
against the real header before runtime diagnostics. Parsing/compiler fidelity is
trusted; no C++ object, memory, exception or standard-library algorithm theorem
is claimed. Frozen source parsing requires no C++ compiler.
"""
from dataclasses import replace
import hashlib
import math
import re
from .graph import Unsupported,number


TOKEN=re.compile(r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|[A-Za-z_]\w*|\d+(?:\.\d*)?(?:[eEpP][+-]?\d+)?|::|[^\s]')


def admit(source,function,configuration):
    if (not isinstance(configuration,dict) or set(configuration)!={'constants'}
            or not isinstance(configuration['constants'],dict)
            or not re.fullmatch(r'[A-Za-z_]\w*(?:::[A-Za-z_]\w*)*',function)):
        raise Unsupported('cpp_module requires constants and a qualified scalar function name')
    if len(source)>1_000_000 or re.search(r'\\\r?\n|\?\?',source):
        raise Unsupported('C++ source size, line splicing or trigraphs are outside this profile')
    def spaces(m):return ''.join('\n' if c=='\n' else ' ' for c in m[0])
    quoted=r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\''
    clean=re.sub(quoted+r'|/\*.*?\*/|//[^\n]*',
                 lambda m:m[0] if m[0][0] in ('"',"'") else spaces(m),source,flags=re.S)
    if re.search(r'\b(?:u8|u|U|L)?R"',clean):
        raise Unsupported('C++ raw string literals are outside the closed header selector')
    for line in clean.splitlines():
        if line.lstrip().startswith('#') and not (
                re.fullmatch(r'\s*#\s*(?:ifndef|define)\s+[A-Z_][A-Z_0-9]*\s*',line)
                or re.fullmatch(r'\s*#\s*endif\s*',line)
                or re.fullmatch(r'\s*#\s*include\s*<(?:algorithm|cmath|cstdint|limits|type_traits|bit)>\s*',line)):
            raise Unsupported('C++ preprocessing admits empty header guards and the listed standard headers only')
    constants=configuration['constants']
    for name,bits in constants.items():
        if (not re.fullmatch(r'[A-Z_][A-Z_0-9]*',name) or not isinstance(bits,str)
                or not re.fullmatch(r'0x[0-9a-f]{16}',bits) or not math.isfinite(number(int(bits,16)))):
            raise Unsupported('C++ constants need uppercase identifiers and finite exact binary64 words')
    # Mask preprocessing lines for lexical scope scanning, retaining offsets.
    clean=re.sub(r'(?m)^\s*#[^\n]*',spaces,clean)
    tokens=list(TOKEN.finditer(clean));stack=[];found=[]
    names=function.split('::');base=names[-1];namespace=names[:-1]
    for i,token in enumerate(tokens):
        text=token[0]
        if (text=='double' and i+2<len(tokens) and tokens[i+1][0]==base and tokens[i+2][0]=='('
                and all(kind=='namespace' for kind,_ in stack) and [name for _,name in stack]==namespace):
            close=i+3
            while close<len(tokens) and tokens[close][0]!=')':close+=1
            if close+1>=len(tokens) or tokens[close+1][0]!='{':continue
            depth=1;end=close+2
            while end<len(tokens) and depth:
                depth+=int(tokens[end][0]=='{')-int(tokens[end][0]=='}');end+=1
            if depth:raise Unsupported('Unclosed C++ function')
            start=i
            while start and tokens[start-1][0] not in ('{','}',';'):start-=1
            if any(token[0] not in ('static','inline') for token in tokens[start:i]):
                raise Unsupported('C++ selected function admits only optional static/inline prefixes; templates and attributes are outside this profile')
            found.append((tokens[start].start(),tokens[end-1].end()))
        if text=='{':
            stack.append(('namespace',tokens[i-1][0]) if i>=2 and tokens[i-2][0]=='namespace' else ('other',''))
        elif text=='}':
            if not stack:raise Unsupported('Unbalanced C++ scope')
            stack.pop()
    if stack or len(found)!=1:raise Unsupported('Select one unambiguous namespace-level double function')
    start,end=found[0];fragment=clean[start:end]
    for name,bits in constants.items():fragment=re.sub(r'\b'+re.escape(name)+r'\b','('+number(int(bits,16)).hex()+')',fragment)
    from .c_frontend import c_frontend
    program=c_frontend(fragment,base)
    if (program.c['return_type']!='double' or program.c['loops'] or len(program.nodes)>32
            or any(p['kind']!='scalar' for p in program.c['api'])):
        raise Unsupported('C++ currently admits at most 32 straight-line double operations and by-value double parameters')
    return replace(program,language='cpp',function=function,c=None,selection={
        'schema':'cpp-double-module-v1','source_sha256':hashlib.sha256(source.encode()).hexdigest(),
        'byte_range':[len(source[:start].encode()),len(source[:end].encode())],'constants':constants,'standard':'c++20',
        'qualification':'Closed namespace-level scalar function; selected source parsing and compiler/runtime fidelity remain trusted. External constants are checked against the original header by static_assert.'})
