from dimacs_parser import *
from solver import Solver

def main():
    input = "c A sample .cnf file.\np cnf 3 2\n1 -3 0\n2 3 -1 0"
    formula, n_literals = dimacs_parse(input)
    solver = Solver(formula, n_literals)
    assignment, sat_result = solver.dpll_solve()
    print(assignment)
    print(sat_result)

if __name__ == "__main__":
    main()