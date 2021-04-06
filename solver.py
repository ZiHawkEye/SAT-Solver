"""
Defines SAT solver.
"""
from constants import *
from logger import Logger

class Solver:
    def __init__(self, formula, n_vars, isLog=False):
        # a formula is a list of clauses
        # a clause is a set of variables
        # a variable is represented by a integer. -variable represents the negation literal
        self.assigned_lits = {0: []} # { decision_level: [ literal ] } - contains the list of literals in lifo assignment order
        self.unassigned = { i for i in range(1, n_vars + 1) } # { variable }
        self.assignments = {} # { variable: value }
        self.antecedents = {} # { variable: clause_index }
        self.decision_levels = {} # { variable: decision_level }
        self.clause_index_map = {} # { clause: clause_index }
        # invariant: all watched literals have not been assigned yet, or they have been assigned value 1, or they are assigned 0.
        self.literal_clause_watchlist = {} # { literals: [ clause_index ] } - range of literals is [-n: n], where n is the number of variables
        self.clause_literal_watchlist = {} # { clause_index: [ literal ] }

        for i in range(len(formula)):
            clause = formula[i]
            self.clause_index_map[clause] = i

        for l in range(-n_vars, n_vars + 1):
            self.literal_clause_watchlist[l] = []

        for clause_index in range(len(formula)):
            # adds 2 watched literals per clause
            self.add_watched_literal(formula, clause_index)
            self.add_watched_literal(formula, clause_index)

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
                return self.assignments, self.eval_formula(formula)

            if (self.eval_formula(formula) == UNSAT):
                if self.decision_level == 0:
                    return {}, UNSAT

                # conflict analysis to learn new clause and level to backtrack to  
                learnt_clause, stage, uip_literal = self.conflict_analysis(formula) 
                uip_literal_value = self.eval_literal(uip_literal)
                
                # adds the learnt clause to the formula and adds 2 watched literals for the clause
                formula += [learnt_clause]
                self.clause_index_map[learnt_clause] = len(formula) - 1 # maps clause to clause index
                self.add_watched_literal(formula, len(formula) - 1)
                self.add_watched_literal(formula, len(formula) - 1)

                # backtracks assignments 
                self.backtrack(stage)
                self.decision_level = stage

                # adds uip variable assignment to new stage
                self.assign_variable(formula, uip_literal, uip_literal_value, stage)

                continue
            
            if (self.eval_formula(formula) == UNDECIDED):
                # increments decision level after choosing a variable
                variable, value = self.pick_branching_variable()
                self.decision_level += 1 
                self.assign_variable(formula, variable, value, self.decision_level)

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

            # gets the last assigned variable at the current decision level
            # checks for unit clauses containing the variable
            antecedent = None # antecedent is the unit clause where the implication rule is applied

            if (self.decision_level in self.assigned_lits and 
                    self.assigned_lits[self.decision_level] != []):
                last_assigned_var = self.assigned_lits[self.decision_level][-1]
                # only checks clauses where the last assigned variable has value 0
                literal = last_assigned_var

                if self.eval_literal(literal) == 1:
                    literal = -literal
                
                for clause_index in self.literal_clause_watchlist[literal]:
                    clause = formula[clause_index]
                    if self.eval_clause(clause) == UNIT:
                        unit_literal = self.get_unit_literal(clause)
                        antecedent = clause
                        break
            
            # otherwise search for unit clause in the entire formula
            if antecedent == None:
                for clause in formula:
                    if self.eval_clause(clause) == UNIT:
                        unit_literal = self.get_unit_literal(clause)
                        antecedent = clause
                        break

            # terminates if there are no more unit clauses
            if antecedent == None:
                break

            # if all other literals in the clause have value 0, then the last literals must have value 1
            self.assign_variable(formula, unit_literal, 1, self.decision_level, antecedent)

        return formula

    def resolution(self, clause1, clause2, pivot):
        # pivot - literal in clause1 whose negation is in clause2
        # resolved clause contains all literals in both clauses except pivot and its negation
        resolved_clause = { literal for literal in clause1 if literal != pivot }
        resolved_clause |= { literal for literal in clause2 if literal != -pivot }

        return resolved_clause

    def conflict_analysis(self, formula):
        """
        "Backtracks" in the implication graph via resolution until the initial assignments leading to the conflict have been learnt.
        Uses 1-UIP heuristic.
            :param formula: SAT formula.
            :returns: New formula with learnt clause - resolved clauses, stage to backtrack to.
        """
        # returns first literal in the clause at the current decision level that has an antecedent, else None
        def pred(clause):
            for literal in clause:
                if (self.get_antecedent(literal) != None 
                        and self.get_decision_level(literal) == self.decision_level):
                    return literal
            
            return None

        # there is a unique implication point at the current decision level that only has 1 variable assigned in the clause
        # returns the uip variable if found, else returns None
        def get_uip(clause):
            literals = { literal for literal in clause 
                    if self.get_decision_level(literal) == self.decision_level }

            if len(literals) == 1:
                return literals.pop()
                
            return None
        
        # searches clauses watching last assigned literal for unsat clause
        last_assigned_literal = self.assigned_lits[self.decision_level][-1]
        literal = last_assigned_literal if self.eval_literal(last_assigned_literal) == 0 else -last_assigned_literal
        clause_indexes = self.literal_clause_watchlist[literal]
        for clause_index in clause_indexes:
            clause = formula[clause_index]
            if self.eval_clause(clause) == UNSAT:
                learnt_clause = clause
                break

        try:
            self.logger.log("unsat clause: " + str(learnt_clause))
        except:
            # searches the entire formula for the unsat clause
            for i in range(len(formula)):
                clause = formula[i]
                if self.eval_clause(clause) == UNSAT:
                    learnt_clause = clause
                    print(learnt_clause)
                    print(self.clause_literal_watchlist[i])
                    exit()
        
        # resolves in a lifo order of assignment of literals
        for i in range(len(self.assigned_lits[self.decision_level]) - 1, -1, -1):
            # terminates at the first uip
            # guarantee: there is a uip at the first assignment of any stage
            uip_literal = get_uip(learnt_clause)
            if uip_literal != None:
                break

            # finds target variable at the current decision level to use as pivot in resolution
            target_literal = self.assigned_lits[self.decision_level][i]

            self.logger.log("resolved clause: {}, target literal: {}, antecedent: {}".format(
                    str(learnt_clause), str(target_literal), str(self.get_antecedent(target_literal))))
            
            learnt_clause = self.resolution(self.get_antecedent(target_literal), learnt_clause, target_literal)
           
        # backtracking heuristic - highest decision level other than the uip literal
        # if clause only contains uip literal, will return 0
        stage = max({ self.get_decision_level(literal) for literal in learnt_clause 
                if literal != uip_literal }, 
                default=0)

        self.logger.log("learnt clause: {}, stage: {}, uip literal: {}".format(str(learnt_clause), str(stage), str(uip_literal)))
        return frozenset(learnt_clause), stage, uip_literal

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
            if i in self.assigned_lits:
                variables = { abs(literal) for literal in self.assigned_lits[i] }
                self.unassigned |= variables
            
            # sets all assigned variables in decision level to unassigned
            for literal in self.assigned_lits[i]:
                variable = abs(literal)
                self.unassign_variable(variable)

            # removes assigned vars in level
            self.assigned_lits[i] = []

    def assign_variable(self, formula, literal, value, decision_level, antecedent=None):
        variable = abs(literal)
        value = value if literal > 0 else 1 - value
        
        self.logger.log("assign {} = {} @ {} with antecedent {}".format(variable, value, decision_level, str(antecedent)))

        # records assignment
        if self.decision_level not in self.assigned_lits:
            self.assigned_lits[decision_level] = []
        
        # removes from unassigned
        self.unassigned.remove(variable)

        # adds variable to decision level
        self.assigned_lits[decision_level].append(literal)

        # sets value of variable, antecedent, decision_level
        self.assignments[variable] = value
        self.antecedents[variable] = antecedent
        self.decision_levels[variable] = decision_level

        # updates clauses watching literal that has value 0
        self.update_watched_literals(formula, variable)
        
    def unassign_variable(self, literal):
        variable = abs(literal)
        self.assignments[variable] = UNASSIGNED
        self.antecedents[variable] = None
        self.decision_levels[variable] = None

    def get_decision_level(self, literal):
        variable = abs(literal)

        if variable not in self.decision_levels:
            return 0

        return self.decision_levels[variable]

    def get_antecedent(self, literal):
        variable = abs(literal)

        if variable not in self.antecedents:
            return None

        return self.antecedents[variable] 
          
    def eval_formula(self, formula):
        return min({ self.eval_clause(clause) for clause in formula }, default=1) # only possible due to total order on assignments
    
    def eval_clause(self, clause):        
        # lazy implementation
        # note: the eval can return UNDECIDED even when the clause is UNSAT
        # because of the nature of lazy implementation but this is intended
        # since watched literals do not change when another literal is set to 1
        clause_index = self.clause_index_map[clause]
        watched_literals = self.clause_literal_watchlist[clause_index]
        a = watched_literals[0]
        b = watched_literals[-1]

        if self.eval_literal(a) == 1 or self.eval_literal(b) == 1:
            value = SAT
        elif self.eval_literal(a) == 0 and self.eval_literal(b) == 0:
            value = UNSAT
        # if only one literal is unassigned and the other == 0
        elif self.eval_literal(a) + self.eval_literal(b) == UNASSIGNED:
            # print(str(a), str(b))
            value = UNIT
        # if clause contains only 1 literal
        elif self.eval_literal(a) == UNASSIGNED and self.eval_literal(b) == UNASSIGNED and a == b:
            # print(str(a), str(b))
            value = UNIT
        else:
            value = UNDECIDED
        
        return value

    def eval_literal(self, literal):
        is_negated = literal < 0
        variable = abs(literal)

        if variable not in self.assignments:
            return UNASSIGNED
        
        value = self.assignments[variable]
        return value if not is_negated else 1 - value

    def get_unit_literal(self, clause):
        # lazy implementation
        # returns None if clause is non-unit
        if self.eval_clause(clause) != UNIT:
            return None
        
        clause_index = self.clause_index_map[clause]
        watched_literals = self.clause_literal_watchlist[clause_index]
        a = watched_literals[0]
        b = watched_literals[-1]

        if self.eval_literal(a) == UNASSIGNED:
            return a
        else: 
            return b

    def add_watched_literal(self, formula, clause_index):
        # adds 1 new watched literal of value != 0 to the clause if found, else adds new literal of value == 0
        clause = formula[clause_index]

        if clause_index not in self.clause_literal_watchlist:
            self.clause_literal_watchlist[clause_index] = []

        if len(self.clause_literal_watchlist[clause_index]) == 2:
            return

        for literal in clause:
            if self.eval_literal(literal) == 1 and literal not in self.clause_literal_watchlist[clause_index]:
                self.literal_clause_watchlist[literal].append(clause_index)
                self.clause_literal_watchlist[clause_index].append(literal)
                return literal

        for literal in clause:
            if self.eval_literal(literal) == UNASSIGNED and literal not in self.clause_literal_watchlist[clause_index]:
                self.literal_clause_watchlist[literal].append(clause_index)
                self.clause_literal_watchlist[clause_index].append(literal)
                return literal

        for literal in clause:
            if self.eval_literal(literal) == 0 and literal not in self.clause_literal_watchlist[clause_index]:
                self.literal_clause_watchlist[literal].append(clause_index)
                self.clause_literal_watchlist[clause_index].append(literal)
                return literal

    def update_watched_literals(self, formula, variable):
        # literal has value 0
        literal = variable if self.eval_literal(variable) == 0 else -variable

        # removes all clauses watching literal 
        clause_indexes = self.literal_clause_watchlist[literal]
        self.literal_clause_watchlist[literal] = []

        for clause_index in clause_indexes:
            self.clause_literal_watchlist[clause_index].remove(literal)

        # adds new watched literal to above clauses
        for clause_index in clause_indexes:
            clause = formula[clause_index]
            new_literal = self.add_watched_literal(formula, clause_index)
            # print(clause)
            
            # if the clause is unit/unsat, should watch the same literal
            if self.eval_clause(clause) == UNIT or self.eval_clause(clause) == UNSAT:
                self.literal_clause_watchlist[new_literal].pop()
                self.clause_literal_watchlist[clause_index].pop()
                self.literal_clause_watchlist[literal].append(clause_index)
                self.clause_literal_watchlist[clause_index].append(literal)
                