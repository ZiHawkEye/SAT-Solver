"""
Defines SAT solver.
"""
from notation import *
import copy

class Solver:
    def __init__(self, formula, n_vars):
        self.assigned_vars = {} # { decision_level: { variable } }
        self.unassigned = { i for i in range(1, n_vars + 1) }
        self.decision_level = 0

    def assign_variable(self, variable, value, decision_level, antecedent=None):
        print("assign {} = {} @ {} with antecedent {}".format(variable, value, decision_level, str(antecedent)))
        
        # records assignment
        if self.decision_level not in self.assigned_vars:
            self.assigned_vars[decision_level] = set()
        
        self.unassigned.remove(variable)
        self.assigned_vars[decision_level].add(variable)
        Variable(variable, value, antecedent, decision_level)
            
    def cdcl(self, formula):
        """
        Implements CDCL algorithm. 
            :param formula: SAT formula.
            :returns: truth assignment that satisfies the formula
        """
        while True:
            formula = self.unit_propagation(formula)
            if formula.value() == SAT:
                break

            if (formula.value() == UNSAT):
                learnt_clause, stage, uip_variable = self.conflict_analysis(formula) # conflict analysis to learn new clause and level to backtrack to
                print("learnt clause: {}, stage: {}".format(str(learnt_clause), str(stage)))
                    
                if stage < 0:
                    return {}, UNSAT

                uip_variable_value = uip_variable.value()
                # backtracks assignments
                self.backtrack(stage)

                # adds the learnt clause to the formula
                formula = formula.union(Formula({ learnt_clause }))

                self.decision_level = stage

                # adds uip variable assignment to new stage
                self.assign_variable(uip_variable.variable, uip_variable_value, stage)
                                
                # print("new formula: " + str(formula))
                # print("assignments: " + str(Variable.get_assignments()))
                
                continue

            variable, value = self.pick_branching_variable()

            # increments decision level after choosing a variable
            self.decision_level += 1 
        
            self.assign_variable(variable, value, self.decision_level)
            
        return Variable.get_assignments(), formula.value()

    def all_variables_assigned(self):
        return self.unassigned == set()

    def pick_branching_variable(self):
        variable = self.unassigned.pop()
        self.unassigned.add(variable)
        return variable, 0

    def unit_propagation(self, formula):
        """
        Applies unit propagation rules until there are no more unit clauses, or if a conflict is identified.
            :param formula: SAT formula.
            :returns: Modified SAT formula after applying unit clause rule.
        """        
        while True:
            # terminates if there is a conflict
            if formula.value() == UNSAT:
                print("conflict")
                return formula

            # find the first unit clause
            antecedent = None # antecedent is the unit clause where the rule is applied
            
            for clause in formula.clauses:
                unit_variable = clause.get_unit_variable()
                if unit_variable != None:
                    antecedent = clause
                    break
            
            # terminates if there are no more unit clauses
            if antecedent == None:
                break

            # if all other variables in the clause have value 0, then the last variable must have value 1
            value = 0 if unit_variable.is_negated else 1
            self.assign_variable(unit_variable.variable, value, self.decision_level, antecedent)

        return formula

    def resolution(self, clause1, clause2):
        # removes all complementary pairs of variables in the 2 clauses
        resolved_clause = { variable for variable in clause1.variables if variable.negation() not in clause2 }
        resolved_clause |= { variable for variable in clause2.variables if variable.negation() not in clause1 }
        return Clause(resolved_clause)

    def conflict_analysis(self, formula):
        """
        "Backtracks" in the implication graph via resolution until the initial assignments leading to the conflict have been learnt.
        Uses 1-UIP heuristic.
            :param formula: SAT formula.
            :returns: Learnt clause, stage to backtrack to.
        """
        # predicate: returns the first variable in the clause at the current decision level that has an antecedent
        # else returns None
        def pred(clause):
            for variable in clause.variables:
                if variable.get_antecedent() != None and variable.get_decision_level() == self.decision_level:
                    return variable

            return None

        # there is a unique implication point at the current decision level that only has 1 variable assigned in the clause
        # returns the uip variable if found, else returns None
        def get_uip(clause):
            variables = { variable for variable in clause.variables 
                    if variable.get_decision_level() == self.decision_level }

            if len(variables) == 1:
                return variables.pop()
                
            return None

        # starts conflict analysis with the unsatisfied clause
        learnt_clause = [clause for clause in formula.clauses if clause.value() == UNSAT].pop() 
        print("unsat: " + str(learnt_clause))
        
        uip_variable = None
        while True: 
            # terminates at the first uip
            uip_variable = get_uip(learnt_clause)
            if uip_variable != None:
                break
            
            # finds the variables to "backtrack" in the implication graph
            target_variable = pred(learnt_clause)
            if target_variable == None:
                print(self.decision_level)
                print({ str(variable.get_antecedent()) for variable in learnt_clause.variables })
                print({ variable.get_decision_level() for variable in learnt_clause.variables })
                assert target_variable != None

            # print("resolved clause: {}, target variable: {}, antecedent: {}".format(
            #         str(learnt_clause), str(target_variable), str(target_variable.get_antecedent())))
            learnt_clause = self.resolution(learnt_clause, target_variable.get_antecedent())

        # backtracking heuristic - highest decision level other than the uip variable
        # if clause only contains uip variable, will return -1
        stage = max({ variable.get_decision_level() for variable in learnt_clause.variables 
                if variable != uip_variable}, 
                default=-1)

        return learnt_clause, stage, uip_variable

    def backtrack(self, stage):
        """
        Backtracks assignments to the chosen decision level.
            :param stage: Chosen decision level.
            :returns: Restored formula at the given decision level.
        """
        print("backtracking to level " + str(stage))
        # removes changes until start of chosen decision level
        for i in range(stage, self.decision_level + 1):
            # adds to unassigned variables
            variables = set()

            if i in self.assigned_vars:
                variables = self.assigned_vars[i]
                self.unassigned |= variables
            
            # removes assigned vars in chosen level
            self.assigned_vars[i] = set()
            
            for variable in variables:
                # sets value in variables to unassigned
                Variable(variable, UNASSIGNED)