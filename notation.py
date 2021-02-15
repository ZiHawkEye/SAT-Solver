"""
Defines notation classes.
"""

from constants import *

class Formula:
    def __init__(self, clauses):
        self.clauses = frozenset(clauses)
        self.val = None
    
    def __str__(self):
        formula_string = ", ".join([clause.__str__() for clause in self.clauses])
        return formula_string

    def __eq__(self, other):
        return isinstance(other, Formula) and self.clauses == other.clauses

    def value(self):
        # lazy eval
        if self.val != None: 
            return self.val

        val = min({ clause.value() for clause in self.clauses }) # only possible due to total order on assignments
        self.val = val
        return self.val

    def get_unit_clause_variable(self, assignment):
        unit_clause = None
        for clause in self.clauses:
            variable_list = list(clause.variables)
            statuses = [l.evaluate(assignment) for l in variable_list]
            status = max(statuses)
            undecided_variables_index = [index for index, value in enumerate(statuses) if value == ENUM.UNDECIDED]
            if status == ENUM.SAT:
                continue # This clause has been satisfied
            if status == ENUM.UNSAT:
                break # This clause is unsatisfied, can break early
            if len(undecided_variables_index) == 1:
                unit_clause = variable_list[undecided_variables_index[0]]
                break
        return unit_clause

    def __contains__(self, clause):
        return clause in self.clauses

class Clause:
    def __init__(self, variables):
        self.variables = frozenset(variables)
        self.val = None
        self.is_uc = None
    
    def __str__(self):
        return "(" + ", ".join([variable.__str__() for variable in self.variables]) + ")"

    def __hash__(self):
        return hash((v.__str__() for v in self.variables))

    def __eq__(self, other):
        return isinstance(other, Clause) and self.variables == other.variables

    def value(self):
        # lazy eval
        if self.val != None:
            return self.val

        self.val = max({ variable.value() for variable in self.variables }) # only possible due to total order on assignments
        return self.val

    def is_unit_clause(self):
        # returns true iff all variables except 1 are assigned 0
        # lazy eval
        if self.is_uc != None:
            return self.is_uc
        
        false_count = len([variable for variable in self.variables if variable.value() == 0])
        self.is_uc = (len(self.variables) - false_count) == 1
        return self.is_uc

    def __contains__(self, variable):
        return variable in self.variables
        
class Variable:
    assignments = {} # { variable: value }
    antecedents = {} # { variable: antecedent }
    decision_levels = {} # { variable: decision_level }

    @classmethod
    def get_assignments():
        return self.assignments

    def __init__(self, variable, value=None, antecedent=None, decision_level=None):
        self.variable = abs(variable)
        self.is_negated = variable < 0

        if value != None:
            Variable.assignments[variable] = value if not self.is_negated else -value
        
        if antecedent != None:
            Variable.antecedents[variable] = antecedent
        
        if decision_level != None:
            Variable.decision_levels[variable] = decision_level
    
    def __str__(self):
        return str(-1 * self.variable) if self.is_negated else str(self.variable)

    def __hash__(self):
        return hash(self.__str__())

    def __eq__(self, other):
        return isinstance(other, Variable) and self.variable == other.variable and self.is_negated == other.is_negated

    def value(self):
        value = Variable.assignments[self.variable]
        
        if value == UNASSIGNED:
            return UNASSIGNED
        
        return value if not self.is_negated else -value

    def get_antecedent(self):
        return Variable.antecedents[self.variable] if self.variable in Variable.antecedents else None

    def get_decision_level(self):
        return Variable.decision_levels[self.variable] if self.variable in Variable.decision_levels else None