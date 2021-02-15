"""
Defines SAT solver.
"""
import copy
from notation import *

UNSAT = 0 
SAT = 1

class Solver:
    def __init__(self, formula, n_vars):
        self.n_vars = n_vars
        self.removed_clauses = {} # tracks removed clauses at each decision level
        self.added_clauses = {} # tracks added clauses at each decision level
        self.assignments = {} # keeps track of assignments at each decision level
        self.decision_level = 0
        self.unassigned = [i for i in range(1, n_vars + 1)]

    def assign_variable(self, variable, value, antecedent, decision_level):
        # records assignment
        if self.assignments[decision_level] == None:
            self.assignments[decision_level] = []
            
        self.assignments[decision_level] += [variable]
        Variable(variable, value, antecedent, decision_level)

    def dpll(self, formula):
        """
        Implements DPLL algorithm.
            :param formula: SAT formula.
            :param unassigned: stack of unassigned values.
            :returns: truth assignment that satisfies the formula
        """
        while not self.all_variables_assigned():
            variable, value = self.pick_branching_variable(formula) # picks the variable to assign
            self.assign_variable(variable, value, decision_level=self.decision_level)
            self.decision_level += 1 # increments decision level after choosing a variable
            formula = self.unit_propagation(formula)

            if (formula.value() == UNSAT):
                formula, stage = self.conflict_analysis(formula) # conflict analysis to learn new clause and level to backtrack to

                if stage < 0:
                    return UNSAT
                else:
                    self.backtrack(formula, stage)
                    self.decision_level = stage

        return assignments

    def all_variables_assigned(self):
        return self.unassigned == []

    def pick_branching_variable(self, formula):
        variable = self.unassigned.pop()
        return (variable, 0) # TODO: when to return 1?

    def unit_propagation(self, formula):
        # applies unit propagation rules until there are no more unit clauses
        is_unit_clauses = [clause.is_unit_clause() for clause in formula.clauses]

        while (True in is_unit_clauses):
            # find the first unit clause
            antecedent = formula.clauses[is_unit_clauses.index(True)] # antecedent is the unit clause where the rule is applied
            variable = [variable for variable in antecedent.variables if variable.value() != 0].pop()

            # if all other variables in the clause have value 0, then the last variable must have value 1
            value = 1 if variable > 0 else 0
            self.assign_variable(variable, value, antecedent, self.decision_level)
            
            # remove all other clauses containing the literal
            # TODO: add to removed clauses
            clauses = { clause for clause in formula.clauses if variable in clause }

            # remove all negations of the literal in all other clauses
            negation = Variable(-variable.variable)

            remove_literal = lambda variable, clause : (clause 
                    if variable not in clause 
                    else Clause({var for var in clause if var != variable }))
            
            clauses = { remove_literal(negation, clause) for clause in formula.clauses }
            formula = Formula(clauses)
            is_unit_clauses = [clause.is_unit_clause() for clause in formula.clauses]

        return formula

    def resolution(self, clause1, clause2):
        # removes all complementary pairs of variables in the 2 clauses
        resolved_clause = { variable for variable in clause1.variables if Variable(-variable.variable) not in clause2 }
        resolved_clause |= { variable for variable in clause2.variables if Variable(-variable.variable) not in clause1 }
        return Clause(resolved_clause)

    def conflict_analysis(self, formula):
        # "backtracks" via resolution until the initial assignments leading to the conflict have been learnt

        # predicate: returns the first variable in the clause at the current decision level that has an antecedent
        # else returns None
        def pred(clause, level):
            for variable in clause.variables:
                if variable.get_antecedent() != None and variable.get_decision_level() == level:
                    return variable
            return None

        # there is a unit implication point at a decision level that only has 1 variable assigned
        def is_uip(clause, level):
            variables = { variable for variable in clause.variables 
                    if variable.get_decision_level() == level }
            return len(variables) == 1

        learnt_clause = [clause for clause in formula.clauses if clause.value() == UNSAT].pop() # starts with the unsatisfied clause
        target_variable = pred(learnt_clause) # finds the variables to "backtrack"

        # stops at the first uip
        while True: 
            if (is_uip(learnt_clause, target_variable.get_decision_level())):
                break

            # performs resolution on the variable's antecedent
            learnt_clause = self.resolution(learnt_clause, target_variable.get_antecedent())

            target_variable = pred(learnt_clause, target_variable.get_decision_level())
            
        # appends learnt clause to formula
        # TODO: add to added clauses
        new_formula = formula.clauses.union(learnt_clause) 
        # backtracks to the uip decision level
        stage = target_variable.get_decision_level()
        return (Formula(new_formula), stage)

    def backtrack(self, formula, stage):
        # removes assignments prior to chosen level in dict
        # adds to unassigned variables
        # TODO: adds the removed clauses and removes the added clause at each decision level
        for i in range(stage, self.decision_level):
            variables = self.assignments[i]
            self.unassigned += [variable for variable in variables if variable not in self.unassigned]
            self.assignments[i] = []

        # sets value in variables to unassigned
        # note: antecedent and decision level are not set to None
        Variable(variable, UNASSIGNED)

