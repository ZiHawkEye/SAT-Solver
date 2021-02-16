"""
Defines notation classes.
"""

from constants import *

class Formula:
    def __init__(self, clauses):
        self.clauses = frozenset(clauses)
    
    def __str__(self):
        formula_string = ", ".join([str(clause) for clause in self.clauses])
        return formula_string

    def __eq__(self, other):
        return isinstance(other, Formula) and self.clauses == other.clauses

    def value(self):
        return min({ clause.value() for clause in self.clauses }, default=1) # only possible due to total order on assignments

    def __contains__(self, clause):
        return clause in self.clauses

    def union(self, formula):
        clauses = self.clauses.union(formula.clauses)
        return Formula(clauses)

class Clause:
    def __init__(self, variables):
        self.variables = frozenset(variables)
    
    def __str__(self):
        return "(" + ", ".join([str(variable) for variable in self.variables]) + ")"

    def __hash__(self):
        return hash((str(v) for v in self.variables))

    def __eq__(self, other):
        return isinstance(other, Clause) and self.variables == other.variables

    def value(self):
        return max({ variable.value() for variable in self.variables }, default=0) # only possible due to total order on assignments

    def get_unit_variable(self):
        # returns unit variable iff all variables except 1 are assigned 0, else return None
        false_count = len([variable for variable in self.variables if variable.value() == 0])

        if (len(self.variables) - false_count) == 1:
            return [variable for variable in self.variables if variable.value() != 0].pop()
        
        return None

    def __contains__(self, variable):
        return variable in self.variables
        
class Variable:
    assignments = {} # { variable: value }
    antecedents = {} # { variable: antecedent }
    decision_levels = {} # { variable: decision_level }

    @classmethod
    def get_assignments(cls):
        return Variable.assignments

    def __init__(self, variable, value=None, antecedent=None, decision_level=None):
        self.variable = abs(variable)
        self.is_negated = variable < 0

        if value != None:
            Variable.assignments[self.variable] = value if not self.is_negated else 1 - value
        
        if antecedent != None:
            Variable.antecedents[self.variable] = antecedent
        
        if decision_level != None:
            Variable.decision_levels[self.variable] = decision_level
    
    def __str__(self):
        return str(-1 * self.variable) if self.is_negated else str(self.variable)

    def __hash__(self):
        return hash(self.__str__())

    def __eq__(self, other):
        return isinstance(other, Variable) and self.variable == other.variable and self.is_negated == other.is_negated

    def value(self):
        value = Variable.assignments[self.variable]
        return value if not self.is_negated else 1 - value

    def get_antecedent(self):
        return Variable.antecedents[self.variable] if self.variable in Variable.antecedents else None

    def get_decision_level(self):
        return Variable.decision_levels[self.variable] if self.variable in Variable.decision_levels else None
    
    def negation(self):
        variable = Variable(self.variable)

        if not self.is_negated:
            variable.is_negated = True
        
        return variable