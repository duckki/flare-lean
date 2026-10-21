"""Closed scalar Julia/MATLAB grammars; never execute translated source as a proxy."""
from dataclasses import dataclass
import keyword
import re

from .graph import Graph, Unsupported


TOKEN = re.compile(r'(?:\d+\.\d*|\.\d+|\d+)(?:[eE][+-]?\d+)?|[A-Za-z][A-Za-z0-9_]*|::|\.\*|\./|[+*/-]=|[+*/=(),;\[\]-]')
IDENTIFIER = re.compile(r'[A-Za-z][A-Za-z0-9_]*\Z')
RESERVED = set(('function end return if else elseif for while break continue try catch '
                'global persistent local const let begin quote do struct module using import '
                'true false arguments switch case otherwise classdef endfunction').split())
OPS = {'+': 'add', '-': 'sub', '*': 'mul', '/': 'div', '.*': 'mul', './': 'div'}


@dataclass(frozen=True)
class Token:
    text: str
    line: int


def identifier(token):
    if not IDENTIFIER.fullmatch(token.text) or token.text in RESERVED or keyword.iskeyword(token.text):
        raise Unsupported(f'Expected a portable scalar identifier at line {token.line}')
    return token.text


def statements(language, source):
    result, current, depth = [], [], []
    continuation = False
    for line, original in enumerate(source.splitlines(), 1):
        if (language == 'julia' and '#=' in original) or (language == 'matlab' and re.match(r'\s*%[{}]', original)):
            raise Unsupported('Block comments are unsupported; use single-line comments')
        code = original.split('#' if language == 'julia' else '%', 1)[0]
        continuation = False
        if language == 'matlab' and '...' in code:
            head, rest = code.split('...', 1)
            if rest.strip():
                raise Unsupported(f'Only a trailing MATLAB continuation is supported at line {line}')
            code, continuation = head, True
        # Every non-whitespace source character must belong to this grammar.
        position = 0
        while position < len(code):
            if code[position].isspace():
                position += 1
                continue
            match = TOKEN.match(code, position)
            if not match:
                raise Unsupported(f'Unsupported {language} syntax at line {line}: {code[position:position+16]!r}')
            text = match[0]
            position = match.end()
            if text in ('(', '['):
                depth.append(text)
            elif text in (')', ']'):
                if not depth or depth.pop() != {')': '(', ']': '['}[text]:
                    raise Unsupported(f'Unmatched delimiter at line {line}')
            if text == ';':
                if depth:
                    raise Unsupported('Arrays and nested semicolons are unsupported')
                if current:
                    result.append(current)
                    current = []
            else:
                current.append(Token(text, line))
        if not depth and not continuation and current:
            result.append(current)
            current = []
    if depth or continuation:
        raise Unsupported('Unclosed delimiter or continuation')
    if current:
        result.append(current)
    return result


class Reader:
    def __init__(self, tokens):
        self.tokens = tokens
        self.position = 0

    def peek(self):
        return self.tokens[self.position].text if self.position < len(self.tokens) else None

    def take(self, expected=None):
        if self.peek() is None:
            raise Unsupported('Incomplete scalar syntax')
        token = self.tokens[self.position]
        self.position += 1
        if expected is not None and token.text != expected:
            raise Unsupported(f'Expected {expected!r} at line {token.line}, found {token.text!r}')
        return token

    def end(self):
        if self.peek() is not None:
            raise Unsupported(f'Unexpected syntax at line {self.tokens[self.position].line}: {self.peek()!r}')


def argument_list(reader, language):
    reader.take('(')
    inputs = []
    while reader.peek() != ')':
        inputs.append(identifier(reader.take()))
        if language == 'julia' and reader.peek() == '::':
            reader.take()
            reader.take('Float64')
        if reader.peek() != ',':
            break
        reader.take()
    reader.take(')')
    return inputs


class Expression(Reader):
    def __init__(self, tokens, graph):
        super().__init__(tokens)
        self.graph = graph

    def expression(self, precedence=0):
        token = self.take()
        if token.text in ('+', '-'):
            value = self.graph.unary('neg' if token.text == '-' else 'pos', self.expression(30))
        elif token.text == '(':
            value = self.expression()
            self.take(')')
        elif token.text in self.graph.names:
            value = self.graph.names[token.text]
        elif token.text[0].isdigit() or token.text.startswith('.'):
            floating = any(x in token.text for x in '.eE') or self.graph.language == 'matlab'
            value = self.graph.literal(float(token.text) if floating else int(token.text))
        else:
            raise Unsupported(f'Unknown scalar or unsupported call at line {token.line}: {token.text}')
        while self.peek() in OPS:
            operator = self.peek()
            if operator.startswith('.') and self.graph.language != 'matlab':
                raise Unsupported('Julia broadcast operations require a separate adapter')
            level = 10 if operator in ('+', '-') else 20
            if level < precedence:
                break
            self.take()
            value = self.graph.binary(OPS[operator], value, self.expression(level+1))
        return value

    def outputs(self):
        # Permit Julia's common `return (x, y)` as well as `return x, y`.
        if self.peek() == '(' and self.tokens[-1].text == ')':
            depth = 0
            matching = None
            for i, token in enumerate(self.tokens):
                depth += (token.text == '(') - (token.text == ')')
                if depth == 0:
                    matching = i
                    break
            if matching == len(self.tokens)-1:
                return Expression(self.tokens[1:-1], self.graph).outputs()
        values = [self.expression()]
        while self.peek() == ',':
            self.take()
            values.append(self.expression())
        self.end()
        return values


def scalar_frontend(language, source, function):
    rows = statements(language, source)
    if not rows:
        raise Unsupported('Expected one scalar function')
    header = Reader(rows[0])
    declared_outputs = None
    short = header.peek() != 'function'
    if short and language != 'julia':
        raise Unsupported('Expected a MATLAB function declaration')
    if not short:
        header.take('function')
    if language == 'matlab':
        if header.peek() == '[':
            header.take()
            declared_outputs = [identifier(header.take())]
            while header.peek() not in (']', None):
                if header.peek() == ',':
                    header.take()
                declared_outputs.append(identifier(header.take()))
            header.take(']')
        else:
            declared_outputs = [identifier(header.take())]
        header.take('=')
    if identifier(header.take()) != function:
        raise Unsupported('Declared function name does not match selection')
    inputs = argument_list(header, language)
    graph = Graph(language, function, inputs)
    if short:
        if len(rows) != 1:
            raise Unsupported('Only a single short Julia function is supported')
        header.take('=')
        return graph.finish(Expression(header.tokens[header.position:], graph).outputs())
    header.end()
    has_end = [t.text for t in rows[-1]] == ['end']
    if language == 'julia' and (len(rows) < 3 or not has_end):
        raise Unsupported('Expected one complete function ending in end')
    body = rows[1:-1] if has_end else rows[1:]
    outputs = None
    for i, row in enumerate(body):
        if outputs is not None:
            raise Unsupported('Statements after return are unsupported')
        if row[0].text == 'return':
            if language == 'matlab':
                if len(row) != 1 or i != len(body)-1:
                    raise Unsupported('Only a final bare MATLAB return is supported')
            else:
                outputs = Expression(row[1:], graph).outputs()
            continue
        if len(row) > 1 and row[1].text in ('=', '+=', '-=', '*=', '/='):
            name = identifier(row[0])
            value = Expression(row[2:], graph)
            if row[1].text != '=':
                if language != 'julia' or name not in graph.names:
                    raise Unsupported('Only Julia supports admitted scalar updating assignments')
                left = graph.names[name]
                right = value.expression()
                value.end()
                graph.names[name] = graph.binary(OPS[row[1].text[0]], left, right)
            else:
                graph.names[name] = value.expression()
                value.end()
            if language == 'julia' and i == len(body)-1:
                outputs = [graph.names[name]]
        elif language == 'julia' and i == len(body)-1:
            outputs = Expression(row, graph).outputs()
        else:
            raise Unsupported(f'Unsupported scalar statement at line {row[0].line}')
    if language == 'matlab':
        if any(name not in graph.names for name in declared_outputs):
            raise Unsupported('Every declared MATLAB output must be assigned')
        outputs = [graph.names[name] for name in declared_outputs]
    if outputs is None:
        raise Unsupported('Missing scalar return')
    return graph.finish(outputs)
