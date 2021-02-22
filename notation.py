from enums import ENUM

"""
Defines notation classes.
"""


class Formula(object):
    def __init__(self, clauses):
        self.clauses = clauses  # set of clauses

    def to_string(self):
        formula_string = ", ".join([clause.to_string() for clause in self.clauses])
        return formula_string

    def __str__(self):
        return self.to_string()

    def __eq__(self, other):
        return isinstance(other, Formula) and self.clauses == other.clauses

    def evaluate(self, assignment):
        value = min([clause.evaluate(assignment) for clause in self.clauses])
        return value

    def get_unit_clause_literal(self, assignment):
        unit_clause = None
        literal = None
        for clause in self.clauses:
            literal_list = list(clause.literals)
            statuses = [literal.evaluate(assignment) for literal in literal_list]
            status = max(statuses)
            undecided_literals_index = [index for index, value in enumerate(statuses) if value == ENUM.UNDECIDED]
            if status == ENUM.SAT:
                continue  # This clause has been satisfied
            if status == ENUM.UNSAT:
                break  # This clause is unsatisfied, can break early
            if len(undecided_literals_index) == 1:
                unit_clause = clause
                literal = literal_list[undecided_literals_index[0]]
                break
        return unit_clause, literal

    def find_first_unsat_clause(self, assignment):
        for clause in self.clauses:
            if clause.evaluate(assignment) == ENUM.UNSAT:
                return clause
        return None

class Clause(object):
    def __init__(self, literals):
        self.literals = literals  # set of literals

    def to_string(self):
        return "(" + ", ".join([literal.to_string() for literal in self.literals]) + ")"

    def __str__(self):
        return self.to_string()

    def __hash__(self):
        return hash((l.to_string() for l in self.literals))

    def __eq__(self, other):
        return isinstance(other, Clause) and self.literals == other.literals

    def evaluate(self, assignment):
        if len(self.literals) == 0:
            return 0
        statuses = [literal.evaluate(assignment) for literal in self.literals]
        return max(statuses)

    def remove_trivial_literals(self):
        updated_literal_set = set()
        for literal in self.literals:
            if -literal not in self.literals:
                updated_literal_set.add(literal)
        self.literals = updated_literal_set

    @staticmethod
    def resolve(clause1, clause2):
        literals = set()
        for literal in clause1.literals:
            if -literal not in clause2.literals:
                literals.add(literal)

        for literal in clause2.literals:
            if -literal not in clause1.literals:
                literals.add(literal)
        return Clause(literals)


class Literal(object):
    def __init__(self, dimacs_literal_format):
        literal = int(dimacs_literal_format)
        self.literal = abs(literal)
        self.is_negated = literal < 0

    def to_string(self):
        return str(-1 * self.literal) if self.is_negated else str(self.literal)

    def __str__(self):
        return str(-1 * self.literal) if self.is_negated else str(self.literal)

    def __hash__(self):
        return hash(self.to_string())

    def __eq__(self, other):
        return isinstance(other, Literal) and self.literal == other.literal and self.is_negated == other.is_negated

    def __neg__(self):
        string_form = self.to_string()
        negated_string_form = str(int(string_form) * -1)
        return Literal(negated_string_form)

    def evaluate(self, assignment):
        value = assignment[self.literal]
        if self.is_negated:
            return 1 - value
        else:
            return value
