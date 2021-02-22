"""
Helper functions for parsing DIMACS CNF file.
"""
from exceptions import *
from notation import Formula, Clause, Literal
from enums import ENUM


def dimacs_parse(input):
    """
    Reads a DIMACS CNF file, returns clauses.
        :param input: string input
        :raises FileFormatError: when file format is wrong
        :returns: clauses
    """

    parse_error_msg = ("Incorrect format. The correct format is as follows: \n" +
            "An input file starts with comments (each line starts with c). " + 
            "The number of literals and the number of clauses is defined by the line \"p cnf literals clauses\". \n" + 
            "Each of the next lines specifies a clause: a positive literal is denoted by the corresponding number, " + 
            "and a negative literal is denoted by the corresponding negative number. The last number in a line should be zero.\n" + 
            "For example, \n" + 
            "c A sample .cnf file. \n" +  
            "p cnf 3 2 \n" + 
            "1 -3 0 \n" + 
            "2 3 -1 0 \n")

    lines = input.strip().split("\n")
    
    if not (len(input) >= 2): 
        raise FileFormatError(parse_error_msg)

    formula = Formula(set())
    n_clauses = 0
    n_literals = 0
    for line in lines:
        line = line.strip()
        if line[0] == 'c':
            continue
        elif line[0] == 'p':
            n_literals, n_clauses = parse_cnf_args(line)
        else:
            clause = parse_clause(line)
            formula.clauses.add(clause)
    return formula, n_literals


def parse_cnf_args(line):
    cnf_error_msg = "Incorrect format of 2nd line, should be \"p cnf <NUM OF literalS> <NUM OF CLAUSES>\""
    tokens = line.split()

    if not (tokens[0] == "p" and tokens[1] == "cnf" and len(tokens) == 4):
        raise FileFormatError(cnf_error_msg)

    try:
        n_literals = int(tokens[2])
        n_clauses = int(tokens[3])
    except ValueError as e:
        print(e)
        print(cnf_error_msg)

    return n_literals, n_clauses


def parse_clause(line):
    tokens = line.strip().split()
    if not (tokens[-1] == "0"):
        raise FileFormatError("The last number in a clause should be 0.")
    clause = Clause(set())
    try:
        for token in tokens:
            literal = int(token)
            if literal == 0:
                break
            clause.literals.add(Literal(token))
    except ValueError as e:
        print("Literal must be a non-zero number")
        return None
    return clause
