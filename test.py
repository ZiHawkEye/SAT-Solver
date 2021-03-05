import os
from dimacs_parser import *
from solver import *
import time

sat_path =r'./sat_cases'
unsat_path =r'./unsat_cases'

sat_paths = os.listdir(sat_path)
unsat_paths = os.listdir(unsat_path)

for path in sat_paths:
    with open(os.path.join(sat_path, path)) as f:
        test_case = f.read()

    formula, n_vars = dimacs_parse(test_case)
    solver = Solver(formula, n_vars)
    start_time = time.time()
    assignments, value = solver.cdcl(formula)
    end_time = time.time()
    assert value == SAT
    print("{} passed in {}s".format(path, str(end_time - start_time)))

for path in unsat_paths:
    with open(os.path.join(unsat_path, path)) as f:
        test_case = f.read()

    formula, n_vars = dimacs_parse(test_case)
    solver = Solver(formula, n_vars)
    start_time = time.time()
    assignments, value = solver.cdcl(formula)
    end_time = time.time()
    assert value == UNSAT
    print("{} passed in {}s".format(path, str(end_time - start_time)))

if __name__ == "__main__":
    main()