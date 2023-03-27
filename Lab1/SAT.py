from z3 import *


def gen_cons(n):
    p = [[Bool(f'p_{i + 1}_{j + 1}') for j in range(n)] for i in range(n)]

    # There must be a queen in each line
    cons1 = And([Or(p[i]) for i in range(n)])

    # line
    cons2 = And(
        [
            And([Or(Not(p[i][j]), Not(p[i][k])) for k in range(n) for j in range(k)])
            for i in range(n)
        ])

    # There must be a queen in each column
    cons3 = And([Or([p[i][j] for i in range(n)]) for j in range(n)])

    # column
    cons4 = And(
        [
            And([Or(Not(p[i][j]), Not(p[k][j])) for k in range(n) for i in range(k)])
            for j in range(n)
        ])

    def gen(i, i1):
        tmp = []
        for j1 in range(n):
            for j in range(n):
                if i + j == i1 + j1 or i - j == i1 - j1:
                    tmp.append(Or(Not(p[i][j]), Not(p[i1][j1])))
        return And(tmp)

    # diag
    cons5 = And([gen(i, i1) for i1 in range(n) for i in range(i1)])

    return p, And(cons1, cons2, cons3, cons4, cons5)


def main():
    n = int(input('Input N: '))
    solver = Solver()
    p, cons = gen_cons(n)
    solver.add(cons)
    if solver.check() == sat:
        ans = solver.model()
        ans = [['Q' if ans[p[i][j]] else '_' for j in range(n)] for i in range(n)]
        for i in range(n):
            print("".join(ans[i]))


if __name__ == '__main__':
    main()
