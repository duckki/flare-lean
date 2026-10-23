"""Closed Julia Float64/vector grammar, translated only for source-model admission.

Diagnostics always execute the original Julia source. No generated Python is a
substitute for the actual Julia runtime.
"""
import ast
import re

from .graph import Unsupported


LEX=re.compile(r'(?:\d+\.\d*|\.\d+|\d+)(?:[eE][+-]?\d+)?|[A-Za-z][A-Za-z0-9_]*|::|[+*/-]=|[+*/=(),;\[\]{}:-]')
RESERVED={'function','end','for','return','if','while','begin','let','global','local','const','try','catch','using','import','module','struct','true','false'}


class Reader:
    def __init__(self,tokens):self.tokens=tokens;self.i=0
    def peek(self):return self.tokens[self.i] if self.i<len(self.tokens) else None
    def take(self,value=None):
        token=self.peek()
        if token is None or value is not None and token!=value:raise Unsupported('Unsupported Julia array syntax; expected '+str(value))
        self.i+=1;return token
    def name(self):
        value=self.take()
        if not re.fullmatch('[A-Za-z][A-Za-z0-9_]*',value) or value in RESERVED:raise Unsupported('Expected ordinary Julia identifier')
        return value
    def end(self):
        if self.peek() is not None:raise Unsupported('Unexpected Julia array syntax: '+self.peek())
    def expr(self,precedence=0):
        token=self.take()
        if token in ('+','-'):left=ast.UnaryOp(op=ast.UAdd() if token=='+' else ast.USub(),operand=self.expr(30))
        elif token=='(':
            left=self.expr();self.take(')')
        elif re.fullmatch(r'(?:\d+\.\d*|\.\d+|\d+)(?:[eE][+-]?\d+)?',token):
            left=ast.Constant(value=float(token) if any(c in token for c in '.eE') else int(token))
        elif re.fullmatch('[A-Za-z][A-Za-z0-9_]*',token) and token not in RESERVED:left=ast.Name(id=token,ctx=ast.Load())
        else:raise Unsupported('Unsupported Julia expression token '+token)
        while True:
            if self.peek()=='(':
                if not isinstance(left,ast.Name):raise Unsupported('Julia calls require direct names')
                self.take();args=[]
                while self.peek()!=')':
                    args.append(self.expr())
                    if self.peek()!=',':break
                    self.take()
                self.take(')')
                if left.id=='length' and len(args)==1:left=ast.Call(func=ast.Name(id='len',ctx=ast.Load()),args=args,keywords=[])
                elif left.id=='zeros' and len(args)==2 and isinstance(args[0],ast.Name) and args[0].id=='Float64':
                    left=ast.Call(func=ast.Attribute(value=ast.Name(id='np',ctx=ast.Load()),attr='zeros',ctx=ast.Load()),args=args[1:],
                        keywords=[ast.keyword(arg='dtype',value=ast.Attribute(value=ast.Name(id='np',ctx=ast.Load()),attr='float64',ctx=ast.Load()))])
                else:left=ast.Call(func=left,args=args,keywords=[])
            elif self.peek()=='[':
                self.take();index=self.expr();self.take(']')
                # Julia's selected vectors use ordinary one-based indexing.
                left=ast.Subscript(value=left,slice=ast.BinOp(left=index,op=ast.Sub(),right=ast.Constant(value=1)),ctx=ast.Load())
            elif self.peek() in ('+','-','*','/'):
                operator=self.peek();level=10 if operator in ('+','-') else 20
                if level<precedence:break
                self.take();left=ast.BinOp(left=left,op={'+':ast.Add,'-':ast.Sub,'*':ast.Mult,'/':ast.Div}[operator](),right=self.expr(level+1))
            else:break
        return left


def syntax(source):
    rows=[]
    for line,original in enumerate(source.splitlines(),1):
        if '#=' in original:raise Unsupported('Julia block comments are outside this profile')
        code=original.split('#',1)[0];tokens=[];i=0
        while i<len(code):
            if code[i].isspace():i+=1;continue
            match=LEX.match(code,i)
            if not match:raise Unsupported('Unsupported Julia syntax at line '+str(line))
            tokens.append(match[0]);i=match.end()
        if tokens:
            if tokens[-1]==';':tokens.pop()
            if ';' in tokens:raise Unsupported('Use one Julia statement per line')
            rows.append((line,tokens))
    position=0
    def block(in_loop=False):
        nonlocal position
        result=[]
        while position<len(rows):
            line,tokens=rows[position];position+=1;r=Reader(tokens)
            if r.peek()=='end':r.take();r.end();return result
            if r.peek()=='for':
                r.take();name=r.name();r.take('in')
                start=r.expr();r.take(':');stop=r.expr();r.end()
                iterator=ast.Call(func=ast.Name(id='range',ctx=ast.Load()),args=[start,ast.BinOp(left=stop,op=ast.Add(),right=ast.Constant(value=1))],keywords=[])
                node=ast.For(target=ast.Name(id=name,ctx=ast.Store()),iter=iterator,body=block(True),orelse=[])
            elif r.peek()=='return':
                if in_loop:raise Unsupported('Julia loop returns are outside this profile')
                r.take();value=r.expr();r.end();node=ast.Return(value=value)
            else:
                target=r.expr()
                if r.peek() not in ('=','+=','-=','*=','/='):raise Unsupported('Julia array source requires assignments or explicit returns')
                op=r.take();value=r.expr();r.end()
                if not isinstance(target,(ast.Name,ast.Subscript)):raise Unsupported('Unsupported Julia assignment target')
                target.ctx=ast.Store()
                node=ast.Assign(targets=[target],value=value) if op=='=' else ast.AugAssign(target=target,op={'+=':ast.Add,'-=':ast.Sub,'*=':ast.Mult,'/=':ast.Div}[op](),value=value)
            node.lineno=line;result.append(node)
        raise Unsupported('Unclosed Julia array function or loop')
    functions=[]
    while position<len(rows):
        line,tokens=rows[position];position+=1;r=Reader(tokens);r.take('function');name=r.name();r.take('(');args=[]
        while r.peek()!=')':
            argument=r.name();r.take('::');typ=r.take()
            if typ=='Vector':r.take('{');r.take('Float64');r.take('}')
            elif typ!='Float64':raise Unsupported('Julia array parameters require Float64 or Vector{Float64}')
            annotation=ast.Attribute(value=ast.Name(id='np',ctx=ast.Load()),attr='ndarray',ctx=ast.Load()) if typ=='Vector' else ast.Name(id='float',ctx=ast.Load())
            args.append(ast.arg(arg=argument,annotation=annotation))
            if r.peek()!=',':break
            r.take()
        r.take(')');r.end()
        functions.append(ast.FunctionDef(name=name,args=ast.arguments(posonlyargs=[],args=args,vararg=None,kwonlyargs=[],kw_defaults=[],kwarg=None,defaults=[]),body=block(),decorator_list=[],returns=None,lineno=line))
    return ast.fix_missing_locations(ast.Module(body=[ast.Import(names=[ast.alias(name='numpy',asname='np')]),*functions],type_ignores=[]))
