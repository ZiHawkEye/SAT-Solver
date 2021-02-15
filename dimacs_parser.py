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

    comment = parse_comment(lines)
    n_literals, n_clauses = parse_cnf(lines)

    if not (len(lines) == 2 + n_clauses):
        raise FileFormatError("Exceeded number of clauses specified.")

    formula = parse_formula(lines, n_literals)
    return (formula, n_literals)

def parse_comment(lines):
    tokens = lines[0].strip().split()
    
    if not (tokens[0] == "c" and len(tokens) >= 2):
        raise FileFormatError("Incorrect comment format, should be \"c <COMMENT>\"")

    return lines[0][2:]

def parse_cnf(lines):
    cnf_error_msg = "Incorrect format of 2nd line, should be \"p cnf <NUM OF literalS> <NUM OF CLAUSES>\""
    tokens = lines[1].strip().split()

    if not (tokens[0] == "p" and tokens[1] == "cnf" and len(tokens) == 4):
        raise FileFormatError(cnf_error_msg)

    try:
        n_literals = int(tokens[2])
        n_clauses = int(tokens[3])
    except ValueError as e:
        print(e)
        print(cnf_error_msg)

    return (n_literals, n_clauses)

def parse_formula(lines, n_literals):
    formula = set()

    for i in range(2, len(lines)):
        tokens = lines[i].strip().split()
        
        if not (tokens[-1] == "0"):
            raise FileFormatError("The last number in a clause should be 0.")
        
        tokens = tokens[:-1]

        try:
            clause = set()
            for token in tokens:                
                literal = int(token)
            
                if not (abs(literal) <= n_literals):
                    raise FileFormatError("Exceeded number of literals specified.")
                
                clause.add(Literal(literal)) # literal is an integer, with a negative integer denoting a negation of the literal
        except ValueError as e:
            print("Error, literal should be a nonzero number.") 
        formula.add(Clause(clause))

    return Formula(formula)