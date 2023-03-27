from z3 import *


def gen_cons(n):
    q = [Int(f'Q_{i + 1}') for i in range(n)]
    val_c = [And(1 <= q[i], q[i] <= n) for i in range(n)]
    col_c = [Distinct(q)]
    diag_c = [
        If(i == j, True, And(i + q[i] != j + q[j], i + q[j] != j + q[i]))
        for i in range(n) for j in range(i)
    ]
    return q, val_c + col_c + diag_c


def main():
    n = int(input('Input N: '))
    solver = Solver()
    q, cons = gen_cons(n)
    solver.add(cons)
    if solver.check() == sat:
        ans = solver.model()
        ans = [['Q' if ans[q[i]] == j + 1 else '_' for j in range(n)] for i in range(n)]
        for i in range(n):
            print("".join(ans[i]))


if __name__ == '__main__':
    main()
