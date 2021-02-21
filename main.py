from dimacs_parser import *
from solver import Solver
import os


def main():
    with open(os.path.join(os.getcwd(), "tests/test_cases/test_case_3.txt")) as f:
        test_case_3 = f.read()
    formula, n_literals = dimacs_parse(test_case_3)
    solver = Solver(formula, n_literals)
    assignment, sat_result = solver.cdcl_solve()
    print(assignment)

if __name__ == "__main__":
    main()