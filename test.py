"""
Tests SAT solver on SAT and UNSAT benchmarks.
"""

import os
from dimacs_parser import *
from solver import *
import time
import glob

sat_paths = glob.glob(r'./sat_cases' + '/**/*.cnf', recursive=True)
unsat_paths = glob.glob(r'./unsat_cases' + '/**/*.cnf', recursive=True)

if True:
    for sat_path in sat_paths:
        with open(sat_path) as f:
            test_case = f.read()

        formula, n_vars = dimacs_parse(test_case)
        solver = Solver(formula, n_vars)

        start_time = time.time()
        assignments, value = solver.solve()
        end_time = time.time()

        assert value == SAT

        print("{} passed in {}s".format(sat_path, str(end_time - start_time)))

if True:
    for unsat_path in unsat_paths:
        with open(unsat_path) as f:
            test_case = f.read()

        formula, n_vars = dimacs_parse(test_case)
        solver = Solver(formula, n_vars)

        start_time = time.time()
        assignments, value = solver.solve()
        end_time = time.time()

        assert value == UNSAT

        print("{} passed in {}s".format(unsat_path, str(end_time - start_time)))

print("All test cases passed")