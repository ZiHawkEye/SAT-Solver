"""
Defines SAT solver.
"""
from notation import *
from logger import Logger

class Solver:
    def __init__(self, formula, n_vars, isLog=False):
        self.assigned_vars = {} # { decision_level: [ int_variable ] } - contains the list of variables in lifo assignment order
        self.unassigned = { i for i in range(1, n_vars + 1) } # { int_variable }
        self.decision_level = 0
        self.logger = Logger(False)

    def assign_variable(self, variable, value, decision_level, antecedent=None):
        self.logger.log("assign {} = {} @ {} with antecedent {}".format(variable, value, decision_level, str(antecedent)))
        
        # records assignment
        if self.decision_level not in self.assigned_vars:
            self.assigned_vars[decision_level] = []
        
        self.unassigned.remove(variable)
        self.assigned_vars[decision_level].append(variable)
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
                if self.decision_level == 0:
                    return {}, UNSAT

                # conflict analysis to learn new clause and level to backtrack to  
                formula, stage, uip_variable = self.conflict_analysis(formula) 
                uip_variable_value = uip_variable.value()
                
                # backtracks assignments 
                self.backtrack(stage)
                self.decision_level = stage

                # adds uip variable assignment to new stage
                self.assign_variable(uip_variable.variable, uip_variable_value, stage)
   
                continue
            
            if (formula.value() == UNDECIDED):
                # increments decision level after choosing a variable
                variable, value = self.pick_branching_variable()
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
                self.logger.log("conflict")
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

    def resolution(self, clause1, clause2, pivot):
        # pivot - variable in clause1 whose negation is in clause2
        # resolved clause contains all variables in both clauses except pivot and its negation
        resolved_clause = { variable for variable in clause1.variables if variable != pivot }
        resolved_clause |= { variable for variable in clause2.variables if variable != pivot.negation() }

        return Clause(resolved_clause)

    def conflict_analysis(self, formula):
        """
        "Backtracks" in the implication graph via resolution until the initial assignments leading to the conflict have been learnt.
        Uses 1-UIP heuristic.
            :param formula: SAT formula.
            :returns: New formula with learnt clause - resolved clauses, stage to backtrack to.
        """
        # returns first variable in the clause at the current decision level that has an antecedent, else None
        def pred(clause):
            for variable in clause.variables:
                if (variable.get_antecedent() != None 
                        and variable.get_decision_level() == self.decision_level):
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
        self.logger.log("unsat clause: " + str(learnt_clause))
        
        # iterates through assigned vars at current decision level from last to first assigned
        while True: 
            # terminates at the first uip
            uip_variable = get_uip(learnt_clause)
            if uip_variable != None:
                break

            # finds target variable at the current decision level to use as pivot in resolution
            target_variable = pred(learnt_clause)
            assert(target_variable != None)
            self.logger.log("resolved clause: {}, target variable: {}, antecedent: {}".format(
                    str(learnt_clause), str(target_variable), str(target_variable.get_antecedent())))
            
            learnt_clause = self.resolution(learnt_clause, target_variable.get_antecedent(), target_variable)
           
        # backtracking heuristic - highest decision level other than the uip variable
        # if clause only contains uip variable, will return 0
        stage = max({ variable.get_decision_level() for variable in learnt_clause.variables 
                if variable != uip_variable}, 
                default=0)

        # adds the learnt clause to the formula
        formula = formula.union(Formula({ learnt_clause }))

        self.logger.log("learnt clause: {}, stage: {}".format(str(learnt_clause), str(stage)))
        return formula, stage, uip_variable

    def backtrack(self, stage):
        """
        Backtracks assignments to the chosen decision level.
            :param stage: Chosen decision level.
            :returns: Restored formula at the given decision level.
        """
        self.logger.log("backtracking to level " + str(stage))

        # removes changes until start of chosen decision level
        for i in range(stage, self.decision_level + 1):
            # adds to unassigned variables
            if i in self.assigned_vars:
                self.unassigned |= set(self.assigned_vars[i])
            
            # sets all assigned variables in decision level to unassigned
            for variable in self.assigned_vars[i]:
                Variable(variable, UNASSIGNED)

            # removes assigned vars in level
            self.assigned_vars[i] = []
            