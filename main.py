from dimacs_parser import *
from solver import Solver
from config import Config
import os, time

def main():
    print("Solver configurations for {}: ".format(Config.test_case))
    print("PickBranch Heuristic: {}".format(Config.pick_branch_heuristic))
    print("Conflict Analysis Heuristic: {}".format(Config.conflict_analysis_heuristic))
    with open(os.path.join(os.getcwd(), "tests/test_cases/{}".format(Config.test_case))) as f:
        test_case = f.read()
    formula, n_literals = dimacs_parse(test_case)
    solver = Solver(formula, n_literals)
    start_time = time.time()
    assignment, sat_result = solver.cdcl_solve()
    end_time = time.time()
    print("{} is {}".format(Config.test_case, "SAT" if sat_result == ENUM.SAT else "UNSAT"))
    print("Assignment: {}".format(assignment))
    print("Number of unit propagations: {}".format(solver.num_of_unit_prop_calls))
    print("Done in {} seconds".format(end_time - start_time))


if __name__ == "__main__":
    main()