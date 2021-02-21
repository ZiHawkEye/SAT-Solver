from notation import *
from dimacs_parser import dimacs_parse
from solver import Solver
from enums import ENUM
import os

def test_solver_on_test_case_1():
    with open(os.path.join(os.getcwd(), "tests/test_cases/test_case_1.txt")) as f:
        test_case_1 = f.read()
    formula, n_literals = dimacs_parse(test_case_1)

    solver = Solver(formula, n_literals)
    assignment, sat_result = solver.cdcl_solve()
    assert sat_result == ENUM.SAT
    assert assignment[1] == (0, 1)
    assert assignment[3] == (0, 1)

def test_solver_on_test_case_2():
    with open(os.path.join(os.getcwd(), "tests/test_cases/test_case_2.txt")) as f:
        test_case_2 = f.read()
    formula, n_literals = dimacs_parse(test_case_2)

    solver = Solver(formula, n_literals)
    assignment, sat_result = solver.cdcl_solve()
    assert sat_result == ENUM.SAT
    assert solver.num_of_unit_prop_calls == 1

'''def test_solver_on_test_case3():
    with open(os.path.join(os.getcwd(), "tests/test_cases/test_case_3.txt")) as f:
        test_case_3 = f.read()
    formula, n_literals = dimacs_parse(test_case_3)

    solver = Solver(formula, n_literals)
    assignment, sat_result = solver.cdcl_solve()
    assert sat_result == ENUM.SAT'''