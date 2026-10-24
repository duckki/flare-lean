"""A closed scalar f64 Rust grammar. Rust compilation is an independent diagnostic."""
import re
from numerics.graph import Graph,Unsupported
from numerics.frontends.scalar_languages import TOKEN, Token, Expression


def rust_frontend(source,function):
    if '/*' in source or '*/' in source:
        raise Unsupported('Rust block comments require a separate adapter')
    source='\n'.join(line.split('//',1)[0] for line in source.splitlines())
    match=re.fullmatch(r'\s*pub\s+fn\s+([A-Za-z_][A-Za-z_0-9]*)\s*\((.*?)\)\s*->\s*(f64|\(\s*f64\s*,\s*f64\s*\))\s*\{([^{}]*)\}\s*',source,re.S)
    if not match or match[1]!=function:
        raise Unsupported('Rust adapter expects one pub fn with f64 parameters and one/two f64 outputs')
    inputs=[]
    for arg in match[2].split(','):
        m=re.fullmatch(r'\s*([A-Za-z_][A-Za-z_0-9]*)\s*:\s*f64\s*',arg)
        if not m: raise Unsupported('Only named f64 Rust parameters are admitted')
        inputs.append(m[1])
    graph=Graph('rust',function,inputs); mutable=set()
    def expression(text):
        tokens=[];position=0
        while position<len(text):
            if text[position].isspace(): position+=1;continue
            m=TOKEN.match(text,position)
            if not m: raise Unsupported('Unsupported Rust scalar expression: '+text[position:position+16])
            value=m[0]
            if value[0].isdigit() and not any(x in value for x in '.eE'):
                raise Unsupported('Rust floating-point constants must use float literal syntax')
            tokens.append(Token(value,1));position=m.end()
        return Expression(tokens,graph).outputs()
    chunks=[x.strip() for x in match[4].split(';')]
    if chunks[-1]=='': chunks.pop()
    outputs=None
    for i,chunk in enumerate(chunks):
        if outputs is not None: raise Unsupported('Statements after Rust return are unsupported')
        if chunk.startswith('return '):
            outputs=expression(chunk[len('return '):])
        else:
            m=re.fullmatch(r'let\s+(mut\s+)?([A-Za-z_][A-Za-z_0-9]*)(?:\s*:\s*f64)?\s*=\s*(.+)',chunk,re.S)
            assignment=re.fullmatch(r'([A-Za-z_][A-Za-z_0-9]*)\s*([+*/-]?=)\s*(.+)',chunk,re.S)
            if m:
                values=expression(m[3])
                if len(values)!=1: raise Unsupported('Only scalar Rust let bindings are admitted')
                graph.names[m[2]]=values[0]
                mutable.discard(m[2])
                if m[1]: mutable.add(m[2])
            elif assignment:
                name,operator,text=assignment.groups()
                if name not in mutable: raise Unsupported('Rust assignment requires a mutable scalar binding')
                values=expression(text)
                if len(values)!=1: raise Unsupported('Only scalar Rust assignment is admitted')
                graph.names[name]=values[0] if operator=='=' else graph.binary({'+=':'add','-=':'sub','*=':'mul','/=':'div'}[operator],graph.names[name],values[0])
            elif i==len(chunks)-1 and not match[4].rstrip().endswith(';'):
                outputs=expression(chunk)
            else:
                raise Unsupported('Unsupported Rust statement')
    if outputs is None or len(outputs)!=(1 if match[3]=='f64' else 2):
        raise Unsupported('Rust return must match the declared scalar output count')
    return graph.finish(outputs)
