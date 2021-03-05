import os
from dimacs_parser import *
from solver import *
import os
import copy

sat_path =r'./sat_cases'
unsat_path =r'./unsat_cases'

sat_paths = os.listdir(sat_path)
unsat_paths = os.listdir(unsat_path)

for path in sat_paths:
    with open(os.path.join(sat_path, path)) as f:
        test_case = f.read()

    formula, n_vars = dimacs_parse(test_case)
    solver = Solver(formula, n_vars)
    assignments, value = solver.cdcl(formula)
    assert value == SAT
    print("{} passed".format(path))

for path in unsat_paths:
    with open(os.path.join(unsat_path, path)) as f:
        test_case = f.read()

    formula, n_vars = dimacs_parse(test_case)
    solver = Solver(formula, n_vars)
    assignments, value = solver.cdcl(formula)
    assert value == UNSAT
    print("{} passed".format(path))

if __name__ == "__main__":
    main()