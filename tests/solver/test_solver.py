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
    assert formula.evaluate() == ENUM.SAT

def test_solver_on_test_case_2():
    with open(os.path.join(os.getcwd(), "tests/test_cases/test_case_2.txt")) as f:
        test_case_2 = f.read()
    formula, n_literals = dimacs_parse(test_case_2)

    solver = Solver(formula, n_literals)
    assignment, sat_result = solver.cdcl_solve()
    assert sat_result == ENUM.SAT
    assert solver.num_of_unit_prop_calls == 1
    assert formula.evaluate() == ENUM.SAT

def test_solver_on_test_case3():
    with open(os.path.join(os.getcwd(), "tests/test_cases/test_case_3.txt")) as f:
        test_case_3 = f.read()
    formula, n_literals = dimacs_parse(test_case_3)

    solver = Solver(formula, n_literals)
    assignment, sat_result = solver.cdcl_solve()
    assert sat_result == ENUM.SAT
    assert formula.evaluate() == ENUM.SAT

'''
# This test case currently takes too long. :/
def test_solver_on_test_case4():
    with open(os.path.join(os.getcwd(), "tests/test_cases/test_case_4.txt")) as f:
        test_case_4 = f.read()
    formula, n_literals = dimacs_parse(test_case_4)

    solver = Solver(formula, n_literals)
    assignment, sat_result = solver.cdcl_solve()
    assert sat_result == ENUM.UNSAT
    assert formula.evaluate(assignment) == ENUM.UNSAT
'''

def test_solver_on_test_case5():
    with open(os.path.join(os.getcwd(), "tests/test_cases/test_case_5.txt")) as f:
        test_case_5 = f.read()
    formula, n_literals = dimacs_parse(test_case_5)

    solver = Solver(formula, n_literals)
    assignment, sat_result = solver.cdcl_solve()
    assert sat_result == ENUM.SAT
    assert formula.evaluate() == ENUM.SAT

def test_solver_on_test_case6():
    with open(os.path.join(os.getcwd(), "tests/test_cases/test_case_6.txt")) as f:
        test_case_6 = f.read()
    formula, n_literals = dimacs_parse(test_case_6)

    solver = Solver(formula, n_literals)
    assignment, sat_result = solver.cdcl_solve()
    assert sat_result == ENUM.SAT
    assert formula.evaluate() == ENUM.SAT

def test_solver_on_test_case7():
    with open(os.path.join(os.getcwd(), "tests/test_cases/test_case_7.txt")) as f:
        test_case_7 = f.read()
    formula, n_literals = dimacs_parse(test_case_7)

    solver = Solver(formula, n_literals)
    assignment, sat_result = solver.cdcl_solve()
    assert sat_result == ENUM.SAT
    assert formula.evaluate() == ENUM.SAT