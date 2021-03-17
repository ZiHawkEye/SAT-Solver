from dimacs_parser import *
from solver import Solver
from config import Config
import os, time
from einstein import show_assignment

def main():
    print("Solver configurations for {}: ".format(Config.test_case))
    print("PickBranch Heuristic: {}".format(Config.pick_branch_heuristic))
    print("Conflict Analysis Heuristic: {}".format(Config.conflict_analysis_heuristic))
    time_taken_list = []
    if Config.num_of_times_to_run < 1:
        print("Number of times to run cannot be less than 1")
        return
    with open(os.path.join(os.getcwd(), "tests/test_cases/{}".format(Config.test_case))) as f:
        test_case = f.read()
    for i in range(Config.num_of_times_to_run):
        formula, n_literals = dimacs_parse(test_case)
        original_num_clauses = len(formula.clauses)
        solver = Solver(formula, n_literals)
        start_time = time.time()
        assignment, sat_result = solver.cdcl_solve()
        end_time = time.time()
        time_taken_list.append(end_time - start_time)
        print("Trial #{} done...".format(i + 1))
    print("{} is {}".format(Config.test_case, "SAT" if sat_result == ENUM.SAT else "UNSAT"))
    print("Assignment: {}".format(assignment))
    print("Number of unit propagations: {}".format(solver.num_of_unit_prop_calls))
    print("Number of clauses added from CDCL: {}".format(len(solver.formula.clauses) - original_num_clauses))
    print("Trial times: {}".format(time_taken_list))
    print("Average time taken over {} trials: {} seconds".format(Config.num_of_times_to_run,
                                                                 sum(time_taken_list) / Config.num_of_times_to_run))
    show_assignment(assignment)


if __name__ == "__main__":
    main()