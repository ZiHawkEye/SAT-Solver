from notation import *
from dimacs_parser import dimacs_parse
import os

def test_parser_on_test_case_1():
    with open(os.path.join(os.getcwd(), "tests/test_cases/test_case_1.txt")) as f:
        test_case_1 = f.read()
    formula, n_literals = dimacs_parse(test_case_1)
    
    c1l1 = Literal("1")
    c1l2 = Literal("-3")
    clause1 = Clause(set([c1l1, c1l2]))
    c2l1 = Literal("2")
    c2l2 = Literal("3")
    c2l3 = Literal("-1")
    clause2 = Clause(set([c2l1, c2l2, c2l3]))

    correct_formula = Formula(set([clause1, clause2]))
    
    assert n_literals == 3
    assert formula == correct_formula