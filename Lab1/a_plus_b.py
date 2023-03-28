from z3 import Or, And, Not, sat
from z3 import Bool, Solver


def to_binary(a: int, b: int):
    a = '0' + bin(a)[2:]
    b = '0' + bin(b)[2:]
    if len(a) > len(b):
        n = len(a)
        b = (n - len(b)) * '0' + b
    else:
        n = len(b)
        a = (n - len(a)) * '0' + a
    return n, a, b


def to_cons(n: int, a: str, b: str):
    sym_a = [Bool(f'a_{i}') for i in range(n + 1)]
    sym_b = [Bool(f'b_{i}') for i in range(n + 1)]
    cons_a = [
        (sym_a[i] if a[i - 1] == '1' else Not(sym_a[i]))
        for i in range(1, n + 1)
    ]
    cons_b = [
        (sym_b[i] if b[i - 1] == '1' else Not(sym_b[i]))
        for i in range(1, n + 1)
    ]
    return And(And(cons_a), And(cons_b)), sym_a, sym_b


def gen_cons(n, a, b, is_minus):
    c = [Bool(f'c_{i}') for i in range(n + 1)]
    d = [Bool(f'd_{i}') for i in range(n + 1)]
    cons1 = And([(d[i] == (a[i] == (b[i] == c[i]))) for i in range(1, n + 1)])
    cons2 = And([
        (c[i - 1] == Or(And(a[i], b[i]), And(a[i], c[i]), And(b[i], c[i])))
        for i in range(1, n + 1)
    ])
    cons3 = Not(c[n])
    cons4 = c[0] if is_minus else Not(c[0])
    return d, And(cons1, cons2, cons3, cons4)


def formal(n: int, str_a: str, str_b: str, is_minus: bool):
    input_cons, sym_a, sym_b = to_cons(n, str_a, str_b)
    solver = Solver()
    d, calc_cons = gen_cons(n, sym_a, sym_b, is_minus)
    solver.add(And(input_cons, calc_cons))
    if solver.check() == sat:
        model = solver.model()
        ans = ''.join(['1' if model[d[i]] else '0' for i in range(1, n + 1)])
        return int(ans, 2)
    else:
        print('Invalid input!')
        return -1


def plus(a: int, b: int):
    n, str_a, str_b = to_binary(a, b)
    return formal(n, str_a, str_b, False)


def main():
    a, b = map(int, input('Input a and b in one line: ').split())
    print(f'{a} + {b} = {plus(a, b)}')


if __name__ == '__main__':
    main()
