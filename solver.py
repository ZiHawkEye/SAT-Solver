"""
Defines SAT solver.
"""
from constants import *
from logger import Logger

class Solver:
    def __init__(self, formula, n_vars, isLog=False):
        # a formula is a list of clauses
        # a clause is a set of variables
        # a variable is represented by an integer. -variable represents the negation literal
        self.assigned_lits = {0: []} # { decision_level: [ literal ] } - contains the list of literals in lifo assignment order
        self.unassigned = { i for i in range(1, n_vars + 1) } # { variable }
        self.assignments = {} # { variable: value }
        self.antecedents = {} # { variable: clause }
        self.decision_levels = {} # { variable: decision_level }
        self.clause_literal_watchlist = {} # { clause: [ literal ] }
        self.literal_clause_watchlist = {} # { literal: [ clause ] } - range of literals is [-n: n], where n is the number of variables
        self.decision_level = 0
        self.logger = Logger(isLog)

        # initializes watchlist
        for i in range(-n_vars, n_vars + 1):
            self.literal_clause_watchlist[i] = []
            
        for clause in formula:
            self.add_watched_literal(clause)
            self.add_watched_literal(clause)

    def cdcl(self, formula):
        """
        Implements CDCL algorithm. 
            :param formula: SAT formula.
            :returns: truth assignment that satisfies the formula
        """
        while True:
            formula = self.unit_propagation(formula)

            if self.eval_formula(formula) == SAT:   
                return self.assignments, SAT

            if (self.eval_formula(formula) == UNSAT):
                if self.decision_level == 0:
                    return {}, UNSAT

                # conflict analysis to learn new clause and level to backtrack to  
                learnt_clause, stage, uip_literal = self.conflict_analysis(formula) 
                uip_literal_value = self.eval_literal(uip_literal)
                
                # backtracks assignments 
                self.backtrack(stage)
                self.decision_level = stage

                # adds the learnt clause and its watched literals to the formula after backtracking
                formula += [learnt_clause]
                self.add_watched_literal(learnt_clause)
                self.add_watched_literal(learnt_clause)

                # adds uip variable assignment to new stage
                self.assign_variable(uip_literal, uip_literal_value, stage)

                # unit propagation after assigning uip variable
                continue

            if (self.eval_formula(formula) == UNDECIDED):
                # increments decision level after choosing a variable
                variable, value = self.pick_branching_variable()
                self.decision_level += 1 
                self.assign_variable(variable, value, self.decision_level)

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

            # claim: new unit clauses usually watch the last assigned variable
            # except for clauses with 1 variable
            antecedent = None # antecedent is the unit clause where the implication rule is applied
            
            if (self.decision_level in self.assigned_lits
                and self.assigned_lits[self.decision_level] != []):
                last_assigned_lit = self.assigned_lits[self.decision_level][-1]

                # only checks clauses where the last assigned variable has value 0
                literal = (last_assigned_lit 
                        if self.eval_literal(last_assigned_lit) != 1 
                        else -last_assigned_lit)
                
                for clause in self.literal_clause_watchlist[literal]:
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
            self.assign_variable(unit_literal, 1, self.decision_level, antecedent)

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
            else:
                return None
        
        # invariant: unsat clause watches last assigned variable
        # resolution starts with the unsat clause
        last_assigned_literal = self.assigned_lits[self.decision_level][-1]
        literal = (last_assigned_literal 
                if self.eval_literal(last_assigned_literal) == 0 
                else -last_assigned_literal)
        
        for clause in self.literal_clause_watchlist[literal]:
            if self.eval_clause(clause) == UNSAT:
                learnt_clause = clause
                break

        self.logger.log("unsat clause: " + str(learnt_clause))
        
        # performs resolution on learnt clause in a lifo order of assignment of literals
        for i in range(len(self.assigned_lits[self.decision_level]) - 1, -1, -1):
            # terminates at the first uip
            # guarantee: there is a uip at the first assignment of any stage
            uip_literal = get_uip(learnt_clause)

            if uip_literal != None:
                break

            # finds target variable at the current decision level to use as pivot in resolution
            target_literal = self.assigned_lits[self.decision_level][i]

            # edge case: target literal may not be in learnt clause
            if -target_literal not in learnt_clause:
                continue

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

    def assign_variable(self, literal, value, decision_level, antecedent=None):
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
        self.update_watched_literals(literal)
        
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
        # note: the eval can return UNDECIDED even when the clause is SAT
        # because of the nature of lazy implementation but this is intended
        # since watched literals do not change when another literal is set to 1
        # invariant: if clause evals to UNIT/UNSAT, all unwatched literals in clause are assigned 0
        watched_literals = self.clause_literal_watchlist[clause]
        a = watched_literals[0]
        b = watched_literals[-1]

        if self.eval_literal(a) == 1 or self.eval_literal(b) == 1:
            value = SAT
        elif self.eval_literal(a) == 0 and self.eval_literal(b) == 0:
            value = UNSAT
        # if only one literal is unassigned and the other == 0
        elif self.eval_literal(a) + self.eval_literal(b) == UNASSIGNED:
            value = UNIT
        # if clause contains only 1 literal
        elif self.eval_literal(a) == UNASSIGNED and self.eval_literal(b) == UNASSIGNED and a == b:
            value = UNIT
        else:
            value = UNDECIDED
        
        # UNDO
        if value == UNIT:
            try:
                assert(len([literal for literal in clause if self.eval_literal(literal) == UNDECIDED]) == 1)
            except:
                print(clause)
                print(self.clause_literal_watchlist[clause])
                print([self.eval_literal(literal) for literal in clause])
                exit()
                
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
        
        watched_literals = self.clause_literal_watchlist[clause]
        a = watched_literals[0]
        b = watched_literals[-1]

        if self.eval_literal(a) == UNASSIGNED:
            return a
        else: 
            return b

    def add_watched_literal(self, clause):
        # adds 1 new watched literal of value != 0 to the clause if found, else adds new literal of value == 0
        if clause not in self.clause_literal_watchlist:
            self.clause_literal_watchlist[clause] = []

        if len(self.clause_literal_watchlist[clause]) == 2:
            return

        for literal in clause:
            if self.eval_literal(literal) != 0 and literal not in self.clause_literal_watchlist[clause]:
                self.literal_clause_watchlist[literal].append(clause)
                self.clause_literal_watchlist[clause].append(literal)
                return literal
        
        for literal in clause:
            if self.eval_literal(literal) == 0 and literal not in self.clause_literal_watchlist[clause]:
                self.literal_clause_watchlist[literal].append(clause)
                self.clause_literal_watchlist[clause].append(literal)                                  
                return literal

    def update_watched_literals(self, literal):
        # literal has value 0
        literal = literal if self.eval_literal(literal) == 0 else -literal

        # removes all clauses watching literal 
        clauses = self.literal_clause_watchlist[literal]
        
        for clause in clauses:
            self.clause_literal_watchlist[clause].remove(literal)

        self.literal_clause_watchlist[literal] = []

        # adds new watched literal to above clauses
        for clause in clauses:
            new_literal = self.add_watched_literal(clause)

            # if new reference is assigned 0, then restore initial reference
            # avoids edge cases:
            # initial status: UNSAT, status after backtracking: UNDECIDED, lazy eval status: UNIT/UNSAT
            # this occurs because unwatched literals are unassigned before watched literals
            # keeping the invariant: if watched literals eval to UNIT/UNSAT, all other literals in clause are 0
            if self.eval_literal(new_literal) == 0:
                # removes new reference
                self.literal_clause_watchlist[new_literal].pop()
                self.clause_literal_watchlist[clause].pop()
                # restores initial reference
                self.literal_clause_watchlist[literal].append(clause)
                self.clause_literal_watchlist[clause].append(literal)