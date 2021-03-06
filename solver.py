"""
Defines SAT solver.
"""
from notation import *
from logger import Logger

class Solver:
    def __init__(self, formula, n_vars, isLog=False):
        self.assigned_vars = {} # { decision_level: [ variable ] } - contains the list of variables in lifo assignment order
        self.unassigned = { i for i in range(1, n_vars + 1) } # { variable }
        self.assignments = {} # { variable: value }
        self.antecedents = {} # { variable: antecedent }
        self.decision_levels = {} # { variable: decision_level }
        self.decision_level = 0
        self.logger = Logger(True)

    def cdcl(self, formula):
        """
        Implements CDCL algorithm. 
            :param formula: SAT formula.
            :returns: truth assignment that satisfies the formula
        """
        while True:
            formula = self.unit_propagation(formula)

            if self.eval_formula(formula) == SAT:
                break

            if (self.eval_formula(formula) == UNSAT):
                if self.decision_level == 0:
                    return {}, UNSAT

                # conflict analysis to learn new clause and level to backtrack to  
                learnt_clause, stage, uip_variable = self.conflict_analysis(formula) 
                uip_variable_value = self.eval_variable(uip_variable)
                
                # adds the learnt clause to the formula
                formula += [learnt_clause]

                # backtracks assignments 
                self.backtrack(stage)
                self.decision_level = stage

                # adds uip variable assignment to new stage
                self.assign_variable(uip_variable, uip_variable_value, stage)

                continue
            
            if (self.eval_formula(formula) == UNDECIDED):
                # increments decision level after choosing a variable
                variable, value = self.pick_branching_variable()
                self.decision_level += 1 
                self.assign_variable(variable, value, self.decision_level)
                
        return self.assignments, self.eval_formula(formula)

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
            if self.eval_formula(formula) == UNSAT:
                self.logger.log("conflict")
                return formula

            # find the first unit clause
            antecedent = None # antecedent is the unit clause where the rule is applied
            
            for clause in formula:
                unit_variable = self.get_unit_variable(clause)
                if unit_variable != None:
                    antecedent = clause
                    break
            
            # terminates if there are no more unit clauses
            if antecedent == None:
                break

            # if all other variables in the clause have value 0, then the last variable must have value 1
            value = 0 if unit_variable < 0 else 1
            self.assign_variable(unit_variable, value, self.decision_level, antecedent)

        return formula

    def resolution(self, clause1, clause2, pivot):
        # pivot - variable in clause1 whose negation is in clause2
        # resolved clause contains all variables in both clauses except pivot and its negation
        resolved_clause = { variable for variable in clause1 if variable != pivot }
        resolved_clause |= { variable for variable in clause2 if variable != -pivot }

        return resolved_clause

    def conflict_analysis(self, formula):
        """
        "Backtracks" in the implication graph via resolution until the initial assignments leading to the conflict have been learnt.
        Uses 1-UIP heuristic.
            :param formula: SAT formula.
            :returns: New formula with learnt clause - resolved clauses, stage to backtrack to.
        """
        # returns first variable in the clause at the current decision level that has an antecedent, else None
        def pred(clause):
            for variable in clause:
                if (self.get_antecedent(variable) != None 
                        and self.get_decision_level(variable) == self.decision_level):
                    return variable
            
            return None

        # there is a unique implication point at the current decision level that only has 1 variable assigned in the clause
        # returns the uip variable if found, else returns None
        def get_uip(clause):
            variables = { variable for variable in clause 
                    if self.get_decision_level(variable) == self.decision_level }

            if len(variables) == 1:
                return variables.pop()
                
            return None

        # starts conflict analysis with the unsatisfied clause
        learnt_clause = [clause for clause in formula if self.eval_clause(clause) == UNSAT].pop() 
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
                    str(learnt_clause), str(target_variable), str(self.get_antecedent(target_variable))))
            
            learnt_clause = self.resolution(learnt_clause, self.get_antecedent(target_variable), target_variable)

            if learnt_clause == self.get_antecedent(target_variable):
                break
           
        # backtracking heuristic - highest decision level other than the uip variable
        # if clause only contains uip variable, will return 0
        stage = max({ self.get_decision_level(variable) for variable in learnt_clause 
                if variable != uip_variable}, 
                default=0)

        print([self.get_decision_level(variable) for variable in learnt_clause])

        self.logger.log("learnt clause: {}, stage: {}".format(str(learnt_clause), str(stage)))
        return learnt_clause, stage, uip_variable

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
                self.unassign_variable(variable)

            # removes assigned vars in level
            self.assigned_vars[i] = []

    def assign_variable(self, variable, value, decision_level, antecedent=None):
        variable = abs(variable)
        
        self.logger.log("assign {} = {} @ {} with antecedent {}".format(variable, value, decision_level, str(antecedent)))

        # records assignment
        if self.decision_level not in self.assigned_vars:
            self.assigned_vars[decision_level] = []
        
        # removes from unassigned
        self.unassigned.remove(variable)

        # adds variable to decision level
        self.assigned_vars[decision_level].append(variable)

        # sets value of variable, antecedent, decision_level
        self.assignments[variable] = value
        self.antecedents[variable] = antecedent
        self.decision_levels[variable] = decision_level
        
    def unassign_variable(self, variable):
        variable = abs(variable)
        self.assignments[variable] = UNASSIGNED
        self.antecedents[variable] = None
        self.decision_levels[variable] = None

    def get_decision_level(self, variable):
        variable = abs(variable)

        if variable not in self.decision_levels:
            return 0

        return self.decision_levels[variable]

    def get_antecedent(self, variable):
        variable = abs(variable)

        if variable not in self.antecedents:
            return None

        return self.antecedents[variable] 
          
    def eval_formula(self, formula):
        return min({ self.eval_clause(clause) for clause in formula }, default=1) # only possible due to total order on assignments
    
    def eval_clause(self, clause):
        return max({ self.eval_variable(variable) for variable in clause }, default=0) # only possible due to total order on assignments

    def eval_variable(self, variable):
        is_negated = variable < 0
        variable = abs(variable)

        if variable not in self.assignments:
            return UNASSIGNED
        
        value = self.assignments[variable]
        return value if not is_negated else 1 - value

    def get_unit_variable(self, clause):
        # returns None if value of clause is already determined
        if self.eval_clause(clause) != UNDECIDED:
            return None

        # returns unit variable iff all variables except 1 are assigned 0, else return None
        unassigned_variables = [variable for variable in clause if self.eval_variable(variable) == UNASSIGNED]
        if len(unassigned_variables) == 1:
            return unassigned_variables.pop()

        return None
