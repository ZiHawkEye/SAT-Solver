"""
Defines SAT solver.
"""
from notation import *

class Solver:
    def __init__(self, formula, n_vars):
        self.removed_clauses = {} # { decision_level: { removed_clause } }
        self.assigned_vars = {} # { decision_level: { variable } }
        self.unassigned = { i for i in range(1, n_vars + 1) }
        self.decision_level = 0

    def assign_variable(self, variable, value, decision_level, antecedent=None):
        print("assign {} = {} @ {} with antecedent {}".format(variable, value, decision_level, str(antecedent)))
        
        # records assignment
        if self.decision_level not in self.assigned_vars:
            self.assigned_vars[decision_level] = set()
        
        if variable in self.unassigned: # reassignment is legal
            self.unassigned.remove(variable)
            self.assigned_vars[decision_level].add(variable)
            Variable(variable, value, antecedent, decision_level)
            
        print("assignments: " + str(Variable.get_assignments()))

    def cdcl(self, formula):
        """
        Implements CDCL algorithm.
            :param formula: SAT formula.
            :param unassigned: stack of unassigned values.
            :returns: truth assignment that satisfies the formula
        """
        while not self.all_variables_assigned():
            # picks the variable and value to assign
            variable, value = self.pick_branching_variable() 
            # increments decision level after choosing a variable
            self.decision_level += 1 
            self.assign_variable(variable, value, self.decision_level)
            formula = self.unit_propagation(formula)

            if (formula.value() == UNSAT):
                formula, stage = self.conflict_analysis(formula) # conflict analysis to learn new clause and level to backtrack to

                if stage < 0:
                    return {}, UNSAT
                else:
                    formula = self.backtrack(formula, stage)
                    print("new formula: " + str(formula))
                    self.decision_level = stage

        return Variable.get_assignments(), formula.value()

    def all_variables_assigned(self):
        return self.unassigned == set()

    def pick_branching_variable(self):
        variable = self.unassigned.pop()
        self.unassigned.add(variable)
        return variable, 0

    def unit_propagation(self, formula):
        # applies unit propagation rules until there are no more unit clauses, or if a conflict is identified
        while True:
            # checks if there is a conflict
            if formula.value() == UNSAT:
                print("conflict")
                return formula

            # find the first unit clause
            antecedent = None # antecedent is the unit clause where the rule is applied
            
            for clause in formula.clauses:
                if clause.get_unit_variable() != None:
                    unit_variable = clause.get_unit_variable()
                    antecedent = clause
                    break

            if antecedent == None:
                break

            # if all other variables in the clause have value 0, then the last variable must have value 1
            value = 0 if unit_variable.is_negated else 1
            self.assign_variable(unit_variable.variable, value, self.decision_level, antecedent)
            
            # remove all other clauses containing the variable
            # add to removed clauses
            if self.decision_level not in self.removed_clauses:
                self.removed_clauses[self.decision_level] = set()
            self.removed_clauses[self.decision_level] |= { clause for clause in formula.clauses if unit_variable in clause }
            clauses = { clause for clause in formula.clauses if unit_variable not in clause }

            # remove all negations of the variable in all other clauses
            negation = unit_variable.negation()

            remove_literal = lambda variable, clause : (clause 
                    if variable not in clause 
                    else Clause({var for var in clause.variables if var != variable }))
            
            clauses = { remove_literal(negation, clause) for clause in clauses }
            formula = Formula(clauses)

        return formula

    def resolution(self, clause1, clause2):
        # removes all complementary pairs of variables in the 2 clauses
        resolved_clause = { variable for variable in clause1.variables if variable.negation() not in clause2 }
        resolved_clause |= { variable for variable in clause2.variables if variable.negation() not in clause1 }
        return Clause(resolved_clause)

    def conflict_analysis(self, formula):
        # "backtracks" via resolution until the initial assignments leading to the conflict have been learnt

        # predicate: returns the first variable in the clause at the current decision level that has an antecedent
        # else returns None
        def pred(clause):
            for variable in clause.variables:
                if variable.get_antecedent() != None and variable.get_decision_level() == self.decision_level:
                    return variable
            return None

        # there is a unique implication point at the current decision level that only has 1 variable assigned in the clause
        def is_uip(clause):
            variables = { variable for variable in clause.variables 
                    if variable.get_decision_level() == self.decision_level }
            return len(variables) == 1

        learnt_clause = [clause for clause in formula.clauses if clause.value() == UNSAT].pop() # starts with the unsatisfied clause
        
        while True: 
            # stops at the first uip
            if (is_uip(learnt_clause)):
                break

            target_variable = pred(learnt_clause) # finds the variables to "backtrack"
            if target_variable == None:
                # TODO: check if no more backtracking possible in implication graph?
                return formula, -1

            learnt_clause = self.resolution(learnt_clause, target_variable.get_antecedent())

        # appends learnt clause to formula
        formula = Formula(formula.clauses.union({ learnt_clause })) 
        # backtracks to the shallowest decision level of the learnt clause
        stage = min({ variable.get_decision_level() for variable in learnt_clause.variables })
        print("learnt clause: " + str(learnt_clause))
        return formula, stage - 1

    def backtrack(self, formula, stage):
        print("backtracking to level " + str(stage))
        clauses = set().union(formula.clauses)
        for i in range(stage, self.decision_level + 1):
            # adds to unassigned variables
            variables = set()
            if i in self.assigned_vars:
                variables = self.assigned_vars[i]
                self.unassigned |= variables
            # removes assigned vars prior to chosen level
            self.assigned_vars[i] = set()
            # adds the removed clauses at each decision level
            if i in self.removed_clauses:
                clauses |= self.removed_clauses[i]
            self.removed_clauses[i] = set()
            for variable in variables:
                # sets value in variables to unassigned
                # note: antecedent and decision level are not set to None
                Variable(variable, UNASSIGNED) # TODO: ugly

        return Formula(clauses)