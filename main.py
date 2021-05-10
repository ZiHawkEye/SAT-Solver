from dimacs_parser import *
from solver import *
import os
import copy
import time

sat_path =r'./sat_cases'
unsat_path =r'./unsat_cases'
hard_path =r'./hard_cases'

sat_paths = [os.path.join(sat_path, file_path) for file_path in os.listdir(sat_path)]
unsat_paths = [os.path.join(unsat_path, file_path) for file_path in os.listdir(unsat_path)]
hard_paths = [os.path.join(hard_path, file_path) for file_path in os.listdir(hard_path)]

test_case_1 = "c A sample .cnf file.\np cnf 3 2\n1 -3 0\n2 3 -1 0"
test_case_2 = "c Test case 2.\np cnf 5 3\n1 5 -2 0\n1 -3 0\n 2 3 4 0"
test_case_3 = "c Test case 3.\np cnf 8 6\n3 2 -8 0\n3 -7 0\n8 7 4 0\n-4 -5 0\n1 -4 -6 0\n5 6 0"
test_case_4 = "c Test case 4(UNSAT).\np cnf 2 4\n1 2 0\n-1 -2 0\n-1 2 0\n1 -2 0"

def main():
    print("\n".join(sat_paths))    
    print("\n".join(unsat_paths))
    print("\n".join(hard_paths))

    path = hard_paths[0]
    
    with open(os.path.join(os.getcwd(), path)) as f:
        test_case = f.read()

    formula, n_vars = dimacs_parse(test_case)
    print("formula: " + str(formula))

    start_time = time.time()
    solver = Solver(formula, n_vars, isLog=True)

    print(solver.cdcl(formula))
    print("time taken: " + str(time.time() - start_time))

if __name__ == "__main__":
    main()