"""
Defines notation classes.
"""

UNASSIGNED = 0.5 # total order on assignments is 0 < UNASSIGNED < 1

class Formula:
    def __init__(self, clauses):
        self.clauses = frozenset(clauses) # a formula is a set of clauses
        self.value = None
    
    def value(self):
        # lazy eval
        if self.value != None: 
            return self.value

        values = { clause.value() for clause in self.clauses }
        value = min(values) # only possible due to total order on assignments
        self.value = value
        return value

    def __contains__(self, clause):
        return clause in self.clauses

class Clause:
    def __init__(self, variables):
        self.variables = frozenset(variables) # a clause is a set of variables
        self.value = None
        self.is_unit_clause = None
    
    def value(self):
        # lazy eval
        if self.value != None:
            return self.value

        values = { variable.value() for variable in self.variables }
        self.value = max(values) # only possible due to total order on assignments
        return self.value

    def is_unit_clause(self):
        # returns true iff all variables except 1 are assigned 0
        # lazy eval
        if self.is_unit_clause != None:
            return self.is_unit_clauses
        
        false_count = len([variable for variable in self.variables if variable.value() == 0])
        self.is_unit_clause = (len(self.variables) - false_count) == 1
        return self.is_unit_clause

    def __contains__(self, variable):
        return variable in self.variables
        
class Variable:
    assignments = {} # stores all assignments in a static dictionary
    antecedents = {} # stores all antecedents in a static dictionary
    decision_levels = {} # stores all decision_levels in a static dictionary

    def __init__(self, variable, value=None, antecedent=None, decision_level=None):
        self.variable = abs(variable)
        self.negation = lambda x : not x if variable < 0 else lambda x : x

        if value != None:
            Variable.assignments[variable] = self.negation(value)
        
        if antecedent != None:
            Variable.antecedents[variable] = antecedent
        
        if decision_level != None:
            Variable.decision_levels[variable] = decision_level
    
    def value(self):
        value = Variable.assignments[self.variable]
        
        if value == UNASSIGNED:
            return UNASSIGNED
        
        return self.negation(value)

    def get_antecedent(self):
        return Variable.antecedents[self.variable]

    def get_decision_level(self):
        return Variable.decision_levels[self.variable]

    def __eq__(self, other):
        return (isinstance(other, Variable) 
                and other.variable == self.variable
                and other.value() == self.value())