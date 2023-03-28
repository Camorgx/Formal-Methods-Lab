from time import process_time_ns
from pandas import DataFrame
from z3 import *

import SAT
import SMT


def test(method):
    test_n = [i for i in range(4, 41)]
    res = []
    for n in test_n:
        print(f'n = {n}')
        solver = Solver()
        t1 = process_time_ns()
        sym, cons = method.gen_cons(n)
        solver.add(cons)
        t2 = process_time_ns()
        solver.check()
        t3 = process_time_ns()
        res.append([n, t2 - t1, t3 - t2])
    return res


def main():
    print('Begin testing SMT.')
    smt_res = test(SMT)
    print('Test finished.')
    DataFrame(smt_res).to_excel('SMT.xlsx')
    print('Begin testing SAT.')
    smt_res = test(SAT)
    print('Test finished.')
    DataFrame(smt_res).to_excel('SAT.xlsx')


if __name__ == '__main__':
    main()
