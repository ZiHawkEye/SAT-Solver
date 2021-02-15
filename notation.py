from enums import ENUM
"""
Defines notation classes.
"""

class Formula(object):
    def __init__(self, clauses):
        self.clauses = clauses # set of clauses
        
    def to_string(self):
        formula_string = ", ".join([clause.to_string() for clause in self.clauses])
        return formula_string

    def __eq__(self, other):
        return isinstance(other, Formula) and self.clauses == other.clauses

    def evaluate(self, assignment):
        value = min([clause.evaluate(assignment) for clause in self.clauses])
        return value

    def get_unit_clause_literal(self, assignment):
        unit_clause = None
        for clause in self.clauses:
            literal_list = list(clause.literals)
            statuses = [l.evaluate(assignment) for l in literal_list]
            status = max(statuses)
            undecided_literals_index = [index for index, value in enumerate(statuses) if value == ENUM.UNDECIDED]
            if status == ENUM.SAT:
                continue # This clause has been satisfied
            if status == ENUM.UNSAT:
                break # This clause is unsatisfied, can break early
            if len(undecided_literals_index) == 1:
                unit_clause = literal_list[undecided_literals_index[0]]
                break
        return unit_clause

class Clause(object):
    def __init__(self, literals): 
        self.literals = literals # set of literals
    
    def to_string(self):
        return "(" + ", ".join([literal.to_string() for literal in self.literals]) + ")"

    def __hash__(self):
        return hash((l.to_string() for l in self.literals))

    def __eq__(self, other):
        return isinstance(other, Clause) and self.literals == other.literals

    def evaluate(self, assignment):
        statuses = [literal.evaluate(assignment) for literal in self.literals]
        return max(statuses)


class Literal(object):
    def __init__(self, dimacs_literal_format):
        literal = int(dimacs_literal_format)
        self.literal = abs(literal)
        self.is_negated = literal < 0

    def to_string(self):
        return str(-1 * self.literal) if self.is_negated else str(self.literal)

    def __hash__(self):
        return hash(self.to_string())

    def __eq__(self, other):
        return isinstance(other, Literal) and self.literal == other.literal and self.is_negated == other.is_negated

    def evaluate(self, assignment):
        if self.is_negated:
            return 1 - assignment[self.literal]
        else:
            return assignment[self.literal]