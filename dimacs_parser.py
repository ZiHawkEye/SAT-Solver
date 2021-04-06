"""
Helper functions for parsing DIMACS CNF file.
"""
from constants import *
from exceptions import *

def dimacs_parse(input):
    """
    Reads a DIMACS CNF file, returns clauses.
        :param input: string input
        :raises FileFormatError: when file format is wrong
        :returns: clauses
    """

    parse_error_msg = ("Incorrect format. The correct format is as follows: \n" +
            "An input file starts with comments (each line starts with c). " + 
            "The number of variables and the number of clauses is defined by the line \"p cnf variables clauses\". \n" + 
            "Each of the next lines specifies a clause: a positive variable is denoted by the corresponding number, " + 
            "and a negative variable is denoted by the corresponding negative number. The last number in a line should be zero.\n" + 
            "For example, \n" + 
            "c A sample .cnf file. \n" +  
            "p cnf 3 2 \n" + 
            "1 -3 0 \n" + 
            "2 3 -1 0 \n")

    lines = input.strip().split("\n")

    if not (len(input) >= 2): 
        raise FileFormatError(parse_error_msg)

    comments, start = parse_comment(lines)
    n_vars, n_clauses = parse_cnf(lines, start)
    formula = parse_formula(lines, n_vars, n_clauses, start + 1)
    return (formula, n_vars)

def parse_comment(lines):
    hasComment = False
    
    for i in range(len(lines)):
        tokens = lines[i].strip().split()
        
        if not (tokens[0] == "c"):
            if not hasComment:
                raise FileFormatError("Incorrect comment format, should be \"c <COMMENT>\"")

            return lines[0:i], i

        hasComment = True

def parse_cnf(lines, start):
    cnf_error_msg = "Incorrect format of 2nd line, should be \"p cnf <NUM OF VARIABLES> <NUM OF CLAUSES>\""
    tokens = lines[start].strip().split()

    if not (tokens[0] == "p" and tokens[1] == "cnf" and len(tokens) == 4):
        raise FileFormatError(cnf_error_msg)

    try:
        n_vars = int(tokens[2])
        n_clauses = int(tokens[3])
    except ValueError as e:
        print(e)
        print(cnf_error_msg)

    return (n_vars, n_clauses)

def parse_formula(lines, n_vars, n_clauses, start):
    formula = []

    for i in range(start, start + n_clauses):
        tokens = lines[i].strip().split()
        
        if not (tokens[-1] == "0"):
            raise FileFormatError("The last number in a clause should be 0.")
        
        tokens = tokens[:-1]

        try:
            clause = set()

            for token in tokens:                
                variable = int(token)
                clause.add(variable) # variable is an integer, with a negative integer denoting a negation of the variable

        except ValueError as e:
            print("Error, variable should be a nonzero number.")
            
        formula.append(frozenset(clause))

    return formula