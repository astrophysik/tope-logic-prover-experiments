from argparse import ArgumentParser
import yaml
from enum import Enum
from z3 import Int, IntVal, And, BoolVal, Or, Solver, Not, sat, unsat
import re


def read_test_case(filename : str) -> tuple[list[str], list[str], str]:
    with open(filename) as file:
        content = yaml.safe_load(file.read())
        return (content['input']['context'], content['input']['hypotheses'], content['input']['goal'])


def encode_context(context: list[str]):
    env = {}
    coordinates = []

    def allocate(cube_type):
        if cube_type == '2':
            coordinate = f'r{len(coordinates)}'
            coordinates.append(coordinate)
            return coordinate
        if cube_type == '1':
            return ()
        left, right = cube_type
        return allocate(left), allocate(right)

    def bind(pattern, value):
        if isinstance(pattern, str):
            if pattern in env:
                raise ValueError(f'Duplicate binder: {pattern}')
            env[pattern] = value
            return
        if not isinstance(value, tuple) or len(value) != 2:
            raise ValueError('A pair pattern requires a product cube')
        bind(pattern[0], value[0])
        bind(pattern[1], value[1])

    for record in context:
        tokens = re.findall(r'[^\s(),:×]+|[(),:×]', record)
        position = 0

        def peek():
            return tokens[position] if position < len(tokens) else None

        def take(expected=None):
            nonlocal position
            token = peek()
            if token is None or (expected is not None and token != expected):
                raise ValueError(f'Expected {expected or "a token"}, got {token!r}')
            position += 1
            return token

        def parse_pattern():
            if peek() == '(':
                take('(')
                pattern = parse_pattern()
                while peek() == ',':
                    take(',')
                    pattern = (pattern, parse_pattern())
                take(')')
                return pattern
            name = take()
            if not name[0].isalpha() or any(
                not (character.isalnum() or character in "_'-")
                for character in name
            ):
                raise ValueError(f'Invalid binder name: {name!r}')
            return name

        def parse_cube_atom():
            token = take()
            if token in ('2', '𝟚'):
                return '2'
            if token in ('1', '𝟙'):
                return '1'
            if token == '(':
                cube_type = parse_cube_type()
                take(')')
                return cube_type
            raise ValueError(f'Unknown cube type: {token!r}')

        def parse_cube_type():
            cube_type = parse_cube_atom()
            while peek() == '×':
                take('×')
                cube_type = (cube_type, parse_cube_atom())
            return cube_type

        pattern = parse_pattern()
        take(':')
        cube_type = parse_cube_type()
        if peek() is not None:
            raise ValueError(f'Unexpected token: {peek()!r}')
        bind(pattern, allocate(cube_type))

    return env, coordinates


def encode_term(term, env):
    tokens = re.findall(r'π[₁₂]|[(),]|[^\s(),]+', term)
    position = 0

    def peek():
        return tokens[position] if position < len(tokens) else None

    def take(expected=None):
        nonlocal position
        token = peek()
        if token is None or (expected is not None and token != expected):
            raise ValueError(f'Expected {expected or "a term"}, got {token!r}')
        position += 1
        return token

    def parse_term():
        token = take()
        if token in ('0₂', '0'):
            return '0'
        if token in ('1₂', '1'):
            return '1'
        if token in ('⋆', '*'):
            return ()
        if token in ('π₁', 'π₂'):
            value = parse_term()
            if not isinstance(value, tuple) or len(value) != 2:
                raise ValueError(f'{token} requires a pair, got {value!r}')
            return value[0 if token == 'π₁' else 1]
        if token == '(':
            value = parse_term()
            while peek() == ',':
                take(',')
                value = (value, parse_term())
            take(')')
            return value
        if token not in env:
            raise ValueError(f'Unknown cube variable: {token!r}')
        return env[token]

    result = parse_term()
    if peek() is not None:
        raise ValueError(f'Unexpected token: {peek()!r}')
    return result

def encode_interval(value, ranks, n):
    if value == "0":
        return IntVal(0)
    elif value == "1":
        return IntVal(n + 1)
    else:
        return ranks[value]

def encode_equal(left, right, ranks, n):
    if isinstance(left, str) and isinstance(right, str):
        return encode_interval(left, ranks, n) == encode_interval(right, ranks, n)
    elif isinstance(left, tuple) and isinstance(right, tuple) and len(left) == 2 and len(right) == 2:
        return And(encode_equal(left[0], right[0], ranks, n), encode_equal(left[1], right[1], ranks, n))
    elif left == () and right == ():
        return BoolVal(True)
    else:
        raise ValueError("Incompleteble types in equal")

def encode_leq(left, right, ranks, n):
    if isinstance(left, str) and isinstance(right, str):
        return encode_interval(left, ranks, n) <= encode_interval(right, ranks, n)
    else:
        raise ValueError("Incompleteble types in leq")


def encode_formula(text, env, ranks, n):
    text = text.strip()
    if text.startswith('(') and text.endswith(')'):
        balance = 0
        first_balance_zero = -1
        for pos in range(0, len(text)):
            if text[pos] == '(':
                balance += 1
            elif text[pos] == ')':
                balance -= 1
                if balance == 0 and first_balance_zero == -1:
                    first_balance_zero = pos
        if first_balance_zero == len(text) - 1:
            return encode_formula(text[1:-1], env, ranks, n)
    
    balance = 0
    for pos in range(0, len(text)):
        if text[pos] == '(':
            balance += 1
        elif text[pos] == ')':
            balance -= 1
        elif text[pos] == '∨' and balance == 0:
            return Or(encode_formula(text[0:pos], env, ranks, n), encode_formula(text[pos + 1:], env, ranks, n))
    
    balance = 0
    for pos in range(0, len(text)):
        if text[pos] == '(':
            balance += 1
        elif text[pos] == ')':
            balance -= 1
        elif text[pos] == '∧' and balance == 0:
            return And(encode_formula(text[0:pos], env, ranks, n), encode_formula(text[pos + 1:], env, ranks, n))

    if text == "⊥":
        return BoolVal(False)
    elif text == "⊤":
        return BoolVal(True)

    balance = 0
    for pos in range(0, len(text)):
        if text[pos] == '(':
            balance += 1
        elif text[pos] == ')':
            balance -= 1
        elif text[pos] == '≡' and balance == 0:
            return encode_equal(encode_term(text[0:pos], env), encode_term(text[pos + 1:], env), ranks, n)

    balance = 0
    for pos in range(0, len(text)):
        if text[pos] == '(':
            balance += 1
        elif text[pos] == ')':
            balance -= 1
        elif text[pos] == '≤' and balance == 0:
            return encode_leq(encode_term(text[0:pos], env), encode_term(text[pos + 1:], env), ranks, n)

    raise ValueError(f"Unsupported formula: {text!r}")

def decode_model_value(value, ranks, model):
    if isinstance(value, str): 
        return model.eval(ranks[value], model_completion=True).as_long()
    if value == ():
        return ()

    return (decode_model_value(value[0], ranks, model), decode_model_value(value[1], ranks, model))


if (__name__ == "__main__"):
    parser = ArgumentParser(prog="oracle",
                            description="Oracle for simplicial logic which is based on Z3")
    parser.add_argument('input')
    args = parser.parse_args()
    try:
        context, hypotheses, goal = read_test_case(args.input)
        env, coordinates = encode_context(context)
        ranks = {}
        for coordinate in coordinates:
            ranks[coordinate] = Int(coordinate)
        n = len(coordinates)

        solver = Solver()
        for rank in ranks.values():
            solver.add(rank >= encode_interval("0", ranks, n))
            solver.add(rank <= encode_interval("1", ranks, n))

        for hypothesis in hypotheses:
            solver.add(encode_formula(hypothesis, env, ranks, n))

        solver.add(Not(encode_formula(goal, env, ranks, n)))

        result = solver.check()
        if result == sat:
            print("underivable")
            model = solver.model()
            values = []
            for cube in env:
                values.append(str(cube) + " " + str(decode_model_value(env[cube], ranks, model)))
            print("countermodel " + ', '.join(values))
        else:
            print("derivable")

    except FileNotFoundError:
        print("input file not found")



