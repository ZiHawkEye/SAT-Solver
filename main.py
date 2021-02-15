from dimacs_parser import *
from solver import *

def main():
    input = "c A sample .cnf file.\np cnf 3 2\n1 -3 0\n2 3 -1 0"
    formula, n_vars = dimacs_parse(input)
    print(formula, n_vars)

    solver = Solver(formula, n_vars)

    print(solver.cdcl(formula))

if __name__ == "__main__":
    main()