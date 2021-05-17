from dimacs_parser import *
from solver import *
import os
import copy
import time
import glob

sat_paths = glob.glob(r'./sat_cases' + '/**/*.cnf', recursive=True)
unsat_paths = glob.glob(r'./unsat_cases' + '/**/*.cnf', recursive=True)

test_case_1 = "c A sample .cnf file.\np cnf 3 2\n1 -3 0\n2 3 -1 0"
test_case_2 = "c Test case 2.\np cnf 5 3\n1 5 -2 0\n1 -3 0\n 2 3 4 0"
test_case_3 = "c Test case 3.\np cnf 8 6\n3 2 -8 0\n3 -7 0\n8 7 4 0\n-4 -5 0\n1 -4 -6 0\n5 6 0"
test_case_4 = "c Test case 4(UNSAT).\np cnf 2 4\n1 2 0\n-1 -2 0\n-1 2 0\n1 -2 0"

def main():
    # print("\n".join(sat_paths))    
    # print("\n".join(unsat_paths))

    # path = unsat_paths[2]
    # path = sat_paths[4]
    path = r'unsat_cases/pigeon-hole/hole8.cnf'

    with open(os.path.join(os.getcwd(), path)) as f:
        test_case = f.read()

    formula, n_vars = dimacs_parse(test_case)
    print("formula: " + str(formula))

    start_time = time.time()
    solver = Solver(formula, n_vars)
    solver.solve()
    print("time taken: " + str(time.time() - start_time))

if __name__ == "__main__":
    main()