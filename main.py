from dimacs_parser import *
from solver import *

def main():
    test_case_1 = "c A sample .cnf file.\np cnf 3 2\n1 -3 0\n2 3 -1 0"
    test_case_2 = "c Implication graph without conflict.\np cnf 5 3\n1 5 -2 0\n1 -3 0\n 2 3 4 0"

    formula, n_vars = dimacs_parse(test_case_2)
    print(formula, n_vars)

    solver = Solver(formula, n_vars)

    print(solver.cdcl(formula))

if __name__ == "__main__":
    main()