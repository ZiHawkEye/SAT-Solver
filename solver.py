"""
Defines SAT solver.
"""
from constants import *
from logger import Logger
import copy

class Solver:
    def __init__(self, formula, n_vars, isLog=False):
        """
        Initializes solver. 
            :param formula: SAT formula.
            :param n_vars: Number of variables in formula.
            :param isLog: Switch variable that logs activity if True and not otherwise.
        """
        # a formula is a set of clauses
        # a clause is a set of variables
        # a variable is represented by an integer. -variable denotes the negation literal
        # range of literals is [-n: n], where n is the number of variables

        self.formula = copy.deepcopy(formula)
        self.trail = {0: []} # { decision_level: [ literal ] } - contains the list of literals each decision level in lifo assignment order
        self.unassigned = [ i for i in range(1, n_vars + 1) ] # { variable }
        self.assignments = {} # { variable: value }
        self.antecedents = {} # { variable: clause }
        self.decision_levels = {} # { variable: decision_level }
        self.decision_level = 0
        self.logger = Logger(isLog)
        
        # the watched literals heuristic has each clause watching 2 literals, maintaining the following invariant:
        # if watched literals eval to UNIT/UNSAT, all other literals in clause are 0
        # this means that the last 2 assigned literals of a UNIT/UNSAT clause are always watched
        # this speeds up finding unit clauses for propagation and unsat clause for conflict analysis
        self.clause_literal_watchlist = {} # { clause: [ literal ] }
        self.literal_clause_watchlist = {} # { literal: [ clause ] } 
        
        # initializes watchlist
        for literal in range(-n_vars, n_vars + 1):
            self.literal_clause_watchlist[literal] = []
            
        # each clause watches 2 literals
        for clause in formula:
            self.add_watched_literal(clause)
            self.add_watched_literal(clause)
        
        # vsids heuristic dynamically tracks the number of times a variable appears in a formula
        # an unassigned variable with the highest number of appearances is chosen and 
        # assigned a value at the start of each decision level
        # the count for each variable decays after a set interval
        # initializes vsids counter
        self.vsids_counter = {} # { literal: count }
        self.countdown_max_time = 100
        self.countdown = self.countdown_max_time

        # NOTE: implements a variable counter but the ZChaff paper mentions a literal counter of each polarity
        for variable in range(1, n_vars + 1):
            self.vsids_counter[variable] = 0

        for clause in formula:
            for literal in clause:
                self.vsids_counter[abs(variable)] += 1

    def solve(self):
        return self.cdcl(copy.deepcopy(self.formula))

    def cdcl(self, formula):
        """
        Implements CDCL algorithm. 
            :param formula: SAT formula.
            :returns: truth assignment that satisfies the formula
        """
        while True:
            formula = self.unit_propagation(formula)

            if self.eval_formula(formula) == SAT:   
                return self.assignments, self.eval_formula(self.formula)

            if (self.eval_formula(formula) == UNSAT):
                if self.decision_level == 0:
                    return {}, UNSAT

                learnt_clause, stage = self.conflict_analysis(formula) 
                
                self.backtrack(stage)
                self.decision_level = stage

                # adds the learnt clause to the formula after backtracking
                formula.add(learnt_clause)
                self.initialize_learnt_clause(learnt_clause)

                # continue with unit propagation
                continue

            if (self.eval_formula(formula) == UNDECIDED):
                # increments decision level after choosing a variable
                variable, value = self.pick_branching_variable()
                self.decision_level += 1 
                self.assign_variable(variable, value, self.decision_level)

    def pick_branching_variable(self):
        # uses vsids heuristic - takes the variable with the highest count
        self.unassigned.sort(key=lambda variable: self.vsids_counter[variable])
        variable = self.unassigned[-1]
        return variable, 0

    def unit_propagation(self, formula):
        """
        Applies unit propagation rules until there are no more unit clauses, or if a conflict is identified.
            :param formula: SAT formula.
            :returns: Modified SAT formula after applying unit clause rule.
        """        
        while True:
            if self.eval_formula(formula) == UNSAT:
                self.logger.log("conflict")
                return formula

            # claim: new unit clauses usually watch the last assigned literal
            # not necessarily true for clauses with 1 literal
            antecedent = None # antecedent is the unit clause where the implication rule is applied
            
            if (self.decision_level in self.trail
                and self.trail[self.decision_level] != []):
                last_assigned_literal = self.trail[self.decision_level][-1]

                # only checks clauses where the last assigned literal has value 0
                literal = (last_assigned_literal
                        if self.eval_literal(last_assigned_literal) != 1 
                        else -last_assigned_literal)
                
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

            # unit implication rule: if all other literals in the clause have value 0, then the last literal must have value 1
            self.assign_variable(unit_literal, 1, self.decision_level, antecedent)

        return formula

    def resolution(self, clause1, clause2, pivot):
        """
        Performs resolution on 2 clauses with a given pivot
            :param clause1: Clause containing pivot.
            :param clause2: Clause containing negation of pivot.
            :param pivot: Literal in clause1 whose negation is in clause2.
            :returns: Resolved clause containing all literals in both clauses except pivot and its negation.
        """
        resolved_clause = { literal for literal in clause1 if literal != pivot }
        resolved_clause |= { literal for literal in clause2 if literal != -pivot }

        return resolved_clause

    def get_uip(self, learnt_clause):
        """
        Gets the UIP of the learnt clause if it exists.
        There is a unique implication point if the learnt clause only has 1 variable at the current decision level.
            :param learnt_clause: Target clause.
            :returns: Returns the uip variable if found, else returns None.
        """
        literals = [ literal 
                for literal in learnt_clause 
                if self.get_decision_level(literal) == self.decision_level ]

        if len(literals) == 1:
            return literals.pop()
        else:
            return None

    def conflict_analysis(self, formula):
        """
        "Backtracks" in the implication graph via resolution until the initial assignments leading to the conflict have been learnt.
        Uses 1-UIP heuristic.
            :param formula: SAT formula.
            :returns: New formula with learnt clause - resolved clauses, stage to backtrack to.
        """
        # invariant: unsat clause watches last assigned literal
        # conflict analysis starts with the unsat clause
        last_assigned_literal = self.trail[self.decision_level][-1]

        # only checks clauses where the last assigned literal has value 0
        literal = (last_assigned_literal 
                if self.eval_literal(last_assigned_literal) == 0 
                else -last_assigned_literal)
        
        for clause in self.literal_clause_watchlist[literal]:
            if self.eval_clause(clause) == UNSAT:
                learnt_clause = clause
                break

        self.logger.log("unsat clause: " + str(learnt_clause))
        
        # performs resolution on the learnt clause in a lifo order of assignment of literals
        for i in range(len(self.trail[self.decision_level]) - 1, -1, -1):
            # terminates at the first uip
            # guarantee: there is a uip at the first assignment of any decision level
            uip_literal = self.get_uip(learnt_clause)

            if uip_literal != None:
                break

            # finds target literal at the current decision level to use as pivot in resolution
            pivot = self.trail[self.decision_level][i]

            # edge case: pivot's negation may not be in learnt clause - skips over the variable
            if -pivot not in learnt_clause:
                continue

            self.logger.log("resolved clause: {}, target literal: {}, antecedent: {}".format(
                    str(learnt_clause), 
                    str(pivot), 
                    str(self.get_antecedent(pivot))))
            
            learnt_clause = self.resolution(self.get_antecedent(pivot), learnt_clause, pivot)
           
        # backtracks to highest decision level other than the uip literal
        # if clause only contains uip literal, will return 0
        # this ensures learnt clause is always unit after backtracking
        stage = max({ self.get_decision_level(literal) 
                for literal in learnt_clause 
                if literal != uip_literal }, 
                default=0)

        self.logger.log("learnt clause: {}, stage: {}, uip literal: {}".format(
                str(learnt_clause), 
                str(stage), 
                str(uip_literal)))

        return frozenset(learnt_clause), stage

    def backtrack(self, stage):
        """
        Undoes assignments made after the chosen decision level.
            :param stage: Chosen decision level.
            :returns: Restored formula at the given decision level.
        """
        self.logger.log("backtracking to level " + str(stage))

        # removes assignments from all decision levels after stage
        for level in range(stage + 1, self.decision_level + 1):
            if level in self.trail:
                variables = [ abs(literal) for literal in self.trail[level] ]
            
            for literal in self.trail[level]:
                variable = abs(literal)
                self.unassign_variable(variable)

            self.trail[level] = []

    def assign_variable(self, literal, value, decision_level, antecedent=None):
        variable = abs(literal)
        value = (value 
                if literal > 0 
                else 1 - value)
        
        self.logger.log("assign {} = {} @ {} with antecedent {}".format(variable, value, decision_level, str(antecedent)))

        # records assignment
        if self.decision_level not in self.trail:
            self.trail[decision_level] = []

        self.trail[decision_level].append(literal)

        # removes from unassigned
        self.unassigned.remove(variable)
        
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
        self.unassigned.append(variable)

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
        # NOTE: the eval can return UNDECIDED even when the clause is SAT
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
                        
        return value

    def eval_literal(self, literal):
        is_negated = literal < 0
        variable = abs(literal)

        if variable not in self.assignments:
            return UNASSIGNED
        
        value = self.assignments[variable]
        return (value 
                if not is_negated 
                else 1 - value)

    def get_unit_literal(self, clause):
        # lazy implementation
        # returns None if clause is not UNIT
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
        """
        Adds 1 new watched literal of value != 0 to the clause if found, else adds new literal of value == 0
            :param clause: Clause to add watched literal to.
            :returns: New watched literal.
        """
        if clause not in self.clause_literal_watchlist:
            self.clause_literal_watchlist[clause] = []

        if len(clause) == 1 and len(self.clause_literal_watchlist[clause]) == 1:
            # if clause is unit clause
            return 

        for literal in clause:
            if self.eval_literal(literal) != 0 and literal not in self.clause_literal_watchlist[clause]:
                self.literal_clause_watchlist[literal].append(clause)
                self.clause_literal_watchlist[clause].append(literal)
                return literal
        
        # if watched literal = 0, ensures it has the highest decision level in the clause among literals = 0
        # this ensures unwatched literals are not unassigned before watched literals during backtracking
        # thereby keeping watched literals invariant for learnt clauses
        highest = None
        chosen_literal = None

        for literal in clause:
            if self.eval_literal(literal) == 0 and literal not in self.clause_literal_watchlist[clause]:
                if highest == None or highest < self.decision_levels[abs(literal)]:
                    highest = self.decision_levels[abs(literal)]
                    chosen_literal = literal

        literal = chosen_literal
        self.literal_clause_watchlist[literal].append(clause)
        self.clause_literal_watchlist[clause].append(literal)  
        return literal

    def update_watched_literals(self, literal):
        """
        Called when a literal is assigned. Updates watched literals in clauses where the literal's value is 0.
            :param literal: Literal that has been assigned.
            :returns: None.
        """
        # removes all clauses watching literal where literal = 0
        literal = literal if self.eval_literal(literal) == 0 else -literal
        clauses = self.literal_clause_watchlist[literal]
        
        for clause in clauses:
            self.clause_literal_watchlist[clause].remove(literal)

        self.literal_clause_watchlist[literal] = []

        # adds new watched literal to above clauses
        for clause in clauses:
            new_literal = self.add_watched_literal(clause)

            # if new reference is assigned 0, then restore initial reference
            # avoids edge case: initial status: UNSAT, status after backtracking: UNDECIDED, lazy eval status: UNIT/UNSAT
            # this occurs because unwatched literals are unassigned before watched literals during backtracking
            # keeps the invariants: 
            # 1. if watched literals eval to UNIT/UNSAT, all other literals in clause are 0
            # 2. unsat clause always watches last assigned variable
            if self.eval_literal(new_literal) == 0:
                # removes new reference
                self.literal_clause_watchlist[new_literal].pop()
                self.clause_literal_watchlist[clause].pop()
                # restores initial reference
                self.literal_clause_watchlist[literal].append(clause)
                self.clause_literal_watchlist[clause].append(literal)

    def initialize_learnt_clause(self, learnt_clause):
        # adds watched literals for learnt clause and keeps watched literals invariant
        self.add_watched_literal(learnt_clause)
        self.add_watched_literal(learnt_clause)

        # increments vsids counter for all variables in clause
        for literal in learnt_clause:
            self.vsids_counter[abs(literal)] += 1

        # periodically, all counts are right binary shifted as per vsids heuristic
        self.countdown -= 1
        if self.countdown == 0:
            self.countdown = self.countdown_max_time
            for variable in self.vsids_counter.keys():
                self.vsids_counter[variable] = self.vsids_counter[variable] >> 1