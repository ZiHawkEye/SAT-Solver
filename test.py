"""
Tests SAT solver on SAT and UNSAT benchmarks.
"""

import os
from dimacs_parser import *
from solver import *
import time

sat_path =r'./uf50-218'
unsat_path =r'./UUF50.218.1000'

sat_paths = os.listdir(sat_path)
unsat_paths = os.listdir(unsat_path)

for path in sat_paths:
    with open(os.path.join(sat_path, path)) as f:
        test_case = f.read()

    formula, n_vars = dimacs_parse(test_case)
    solver = Solver(formula, n_vars)

    start_time = time.time()
    assignments, value = solver.solve()
    end_time = time.time()

    assert value == SAT

    print("{} passed in {}s".format(path, str(end_time - start_time)))

for path in unsat_paths:
    with open(os.path.join(unsat_path, path)) as f:
        test_case = f.read()

    formula, n_vars = dimacs_parse(test_case)
    solver = Solver(formula, n_vars)

    start_time = time.time()
    assignments, value = solver.solve()
    end_time = time.time()

    assert value == UNSAT

    print("{} passed in {}s".format(path, str(end_time - start_time)))

print("All test cases passed")