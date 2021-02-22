from dimacs_parser import *
from solver import Solver
import os


def main():
    with open(os.path.join(os.getcwd(), "tests/test_cases/test_case_7.txt")) as f:
        test_case = f.read()
    formula, n_literals = dimacs_parse(test_case)
    solver = Solver(formula, n_literals)
    # assignment = {1: (1, 1), 2: (0, 1), 3: (0, 1), 4: (1, 2), 5: (0, 2), 6: (1, 3), 7: (0, 2), 8: (0, 3), 9: (0, 2), 10: (1, 4), 11: (0, 3), 12: (0, 3), 13: (1, 3), 14: (1, 3), 15: (1, 3), 16: (0, 3), 17: (1, 3), 18: (0, 3), 19: (0, 3), 20: (1, 3)}
    # print(formula.find_first_unsat_clause(assignment))
    assignment, sat_result = solver.cdcl_solve()
    print(assignment, sat_result)
    print(formula.evaluate(assignment))

if __name__ == "__main__":

    main()