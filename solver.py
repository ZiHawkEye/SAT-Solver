"""
Defines SAT solver.
"""
from constants import *
from logger import Logger
import copy
from config import *
from collections import defaultdict

class Solver:
    def __init__(self, formula, n_vars):
        """
        Initializes solver. 
            :param formula: SAT formula.
            :param n_vars: Number of variables in formula.
        """
        # a formula is a set of clauses
        # a clause is a set of variables
        # a variable is represented by an integer. -variable denotes the negation literal
        # range of literals is [-n: n], where n is the number of variables

        self.formula = copy.deepcopy(formula)
        self.n_vars = n_vars
        self.trail = defaultdict(lambda: [], {}) # { decision_level: [ literal ] } - contains the list of literals each decision level in lifo assignment order
        self.unassigned = [ i for i in range(1, self.n_vars + 1) ] # { variable }
        self.assignments = defaultdict(lambda: UNASSIGNED, {}) # { variable: value }
        self.antecedents = defaultdict(lambda: None, {}) # { variable: clause }
        self.decision_levels = defaultdict(lambda: 0, {}) # { variable: decision_level }
        self.decision_level = 0
        self.logger = Logger(Config.IS_LOG)

        # recommended by MiniSat - keeps a queue of unit literals
        self.propagation_queue = [] # [ ( literal, antecedent ) ]
        
        # the watched literals heuristic has each clause watching 2 literals, maintaining the following invariant:
        # if watched literals eval to UNIT/UNSAT, all other literals in clause are 0
        # this means that the last 2 assigned literals of a UNIT/UNSAT clause are always watched
        # speeds up finding unit clauses for propagation and unsat clause for conflict analysis
        self.clause_literal_watchlist = defaultdict(lambda: [], {}) # { clause: [ literal ] }
        self.literal_clause_watchlist = defaultdict(lambda: [], {}) # { literal: [ clause ] } 
        
        for literal in range(-self.n_vars, self.n_vars + 1):
            self.literal_clause_watchlist[literal] = []
            
        for clause in formula:
            self.add_watched_literal(clause)
            self.add_watched_literal(clause)
        
        # vsids heuristic dynamically tracks the number of times a variable appears in a formula
        # an unassigned variable with the highest number of appearances is chosen and 
        # assigned a value at the start of each decision level
        # the count for each variable decays after a set interval
        self.is_vsids = Config.IS_VSIDS
        self.vsids_counter = defaultdict(lambda: 0, {}) # { literal: count }
        self.vsids_interval = Config.VSIDS_INTERVAL
        self.vsids_countdown = self.vsids_interval

        # NOTE: implements a variable counter like MiniSat but the ZChaff paper mentions a literal counter
        if self.is_vsids:
            for clause in formula:
                for literal in clause:
                    self.vsids_counter[abs(literal)] += 1

        # after set intervals, the search process will restart by clearing all assignments without deleting learnt clauses
        # the restart interval is extended after every restart
        self.is_restart = Config.IS_RESTART
        self.restart_interval = Config.RESTART_INTERVAL
        self.restart_interval_multiplier = Config.RESTART_MULTIPLIER
        self.restart_countdown = self.restart_interval

        # used in generating proof file
        self.is_proof = Config.IS_PROOF
        self.clauses = [] # [ clause ]
        self.proof = [] # [ ( clause1, clause2, resolved_clause ) ]
        self.clause_index_map = defaultdict(lambda: None, {}) # { clause: index }
        self.output_path = Config.OUTPUT_PATH

        if self.is_proof:
            for clause in formula:
                self.track_clause(clause)

        self.pick_branch_calls = 0

    def solve(self):
        assignments, value = self.cdcl(copy.deepcopy(self.formula))

        if self.is_proof:
            self.generate_proof()

        self.logger.log("Number of pick branch calls: {}".format(self.pick_branch_calls))
        self.logger.log("Value: {}".format(value))
        self.logger.log("Assignments: {}".format(assignments))

        return assignments, value

    def cdcl(self, formula):
        """
        Implements CDCL algorithm. 
            :param formula: SAT formula.
            :returns: truth assignment that satisfies the formula
        """
        while True:
            self.unit_propagation(formula)

            if self.eval_formula(formula) == SAT:   
                return self.assignments, self.eval_formula(self.formula)

            if (self.eval_formula(formula) == UNSAT):
                learnt_clause, stage = self.conflict_analysis(formula) 

                if self.decision_level == 0:            
                    if self.is_proof:
                        self.derive_empty_clause(formula, learnt_clause)

                    return {}, UNSAT

                self.backtrack(stage)
                self.decision_level = stage

                # adds the learnt clause to the formula after backtracking
                formula.add(learnt_clause)
                self.initialize_learnt_clause(learnt_clause)
                
                if not self.is_restart:
                    # clause is always unit after backtracking
                    assert self.eval_clause(learnt_clause) == UNIT
                    self.propagation_queue.append((self.get_unit_literal(learnt_clause), learnt_clause))

                # continue with unit propagation
                continue

            if (self.eval_formula(formula) == UNDECIDED):
                # increments decision level after choosing a variable
                variable, value = self.pick_branching_variable()
                self.decision_level += 1 
                self.assign_variable(variable, value, self.decision_level)

    def pick_branching_variable(self):
        # tracks number of pick branch calls
        self.pick_branch_calls += 1

        # uses vsids heuristic - takes the variable with the highest count
        if self.is_vsids:
            variable = max(self.unassigned, key=lambda variable: self.vsids_counter[variable])
        else:
            variable = self.unassigned[0]
        
        return variable, 0

    def unit_propagation(self, formula):
        """
        Applies unit propagation rules until there are no more unit clauses, or if a conflict is identified.
            :param formula: SAT formula.
            :returns: None.
        """        
        while True:
            if self.eval_formula(formula) == UNSAT:
                self.logger.log("conflict")
                return formula

            antecedent = None # antecedent is the unit clause where the implication rule is applied

            # checks the propagation queue for unit literals
            while self.propagation_queue != []:
                unit_literal, antecedent = self.propagation_queue.pop(0)
                
                if self.eval_clause(antecedent) == UNIT:
                    break
                else:
                    # clauses in the propagation queue might not be unit
                    # due to backtracking or other clauses being visited first
                    unit_literal = None
                    antecedent = None

            # claim: new unit clauses usually watch the last assigned literal
            # not necessarily true for clauses with 1 literal
            # adds all unit literals and clauses to propagation queue
            if (antecedent == None 
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
                        self.propagation_queue.append((unit_literal, antecedent))
            
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

        if self.is_proof:
            self.add_resolution_to_proof(clause1, clause2, frozenset(resolved_clause))
        
        return frozenset(resolved_clause)

    def get_uip(self, learnt_clause):
        """
        Gets the UIP of the learnt clause if it exists.
        There is a unique implication point if the learnt clause only has 1 variable at the current decision level.
            :param learnt_clause: Target clause.
            :returns: Returns the UIP variable if found, else returns None.
        """
        literals = [ literal 
                for literal in learnt_clause 
                if self.get_decision_level(literal) == self.decision_level ]

        if len(literals) == 1:
            return literals[0]
        else:
            return None

    def conflict_analysis(self, formula, is_first_uip=True):
        """
        "Backtracks" in the implication graph via resolution until the initial assignments leading to the conflict have been learnt.
        Uses 1-UIP heuristic.
            :param formula: SAT formula.
            :returns: Learnt clause, stage to backtrack to.
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
        for i in range(len(self.trail[self.decision_level]) + 1):
            # guarantee: there is a uip at the first assignment of any decision level
            uip_literal = self.get_uip(learnt_clause)

            if is_first_uip:
                # terminates at the 1st uip
                if uip_literal != None:
                    break

            # finds target literal at the current decision level to use as pivot in resolution
            pivot = self.trail[self.decision_level][-i]

            # edge case: pivot's negation may not be in learnt clause - skips over the literal
            if -pivot not in learnt_clause:
                continue

            self.logger.log("resolved clause: {}, pivot literal: {}, antecedent: {}".format(
                    str(learnt_clause), str(pivot), str(self.get_antecedent(pivot))))
            
            learnt_clause = self.resolution(self.get_antecedent(pivot), learnt_clause, pivot)
            
        # backtracks to highest decision level other than the uip literal
        # if clause only contains uip literal, will return 0
        # this ensures learnt clause is always unit after backtracking
        stage = max({ self.get_decision_level(literal) 
                for literal in learnt_clause 
                if literal != uip_literal }, 
                default=0)

        self.logger.log("learnt clause: {}, stage: {}, uip literal: {}".format(str(learnt_clause), str(stage), str(uip_literal)))

        return frozenset(learnt_clause), stage

    def backtrack(self, stage):
        """
        Undoes assignments made after the chosen decision level.
            :param stage: Chosen decision level.
            :returns: None.
        """
        self.logger.log("backtracking to level " + str(stage))

        # removes assignments from all decision levels after stage
        for level in range(stage + 1, self.decision_level + 1):
            for literal in self.trail[level]:
                self.unassign_variable(literal)

            self.trail[level] = []

    def assign_variable(self, literal, value, decision_level, antecedent=None):
        variable = abs(literal)
        value = (value 
                if literal > 0 
                else 1 - value)
        
        self.logger.log("assign {} = {} @ {} with antecedent {}".format(variable, value, decision_level, str(antecedent)))

        self.trail[decision_level].append(literal)
        self.unassigned.remove(variable)        
        self.assignments[variable] = value
        self.antecedents[variable] = antecedent
        self.decision_levels[variable] = decision_level

        # updates clauses watching literal of value 0
        self.update_watched_literals(literal)
        
    def unassign_variable(self, literal):
        variable = abs(literal)
        self.unassigned.append(variable)
        self.assignments[variable] = UNASSIGNED
        self.antecedents[variable] = None
        self.decision_levels[variable] = None

    def get_decision_level(self, literal):
        variable = abs(literal)
        return self.decision_levels[variable]

    def get_antecedent(self, literal):
        variable = abs(literal)
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

    def add_watched_literal_ref(self, literal, clause):
        self.literal_clause_watchlist[literal].append(clause)
        self.clause_literal_watchlist[clause].append(literal)

    def remove_watched_literal_ref(self, literal, clause):
        self.literal_clause_watchlist[literal].remove(clause)
        self.clause_literal_watchlist[clause].remove(literal)

    def add_watched_literal(self, clause):
        """
        Adds 1 new watched literal of value != 0 to the clause if found, else adds new literal of value == 0
            :param clause: Clause to add watched literal to.
            :returns: New watched literal.
        """
        if len(clause) == 1 and len(self.clause_literal_watchlist[clause]) == 1:
            # if clause is unit clause
            return 

        if len(self.clause_literal_watchlist[clause]) == 2:
            # to avoid more than 2 references when duplicate clauses are learnt
            return

        for literal in clause:
            if self.eval_literal(literal) != 0 and literal not in self.clause_literal_watchlist[clause]:
                self.add_watched_literal_ref(literal, clause)
                return literal
        
        # if watched literal = 0, ensures it has the highest decision level in the clause among literals = 0
        # this ensures unwatched literals are not unassigned before watched literals during backtracking
        # avoids edge case: initial status: UNSAT, status after backtracking: UNDECIDED, lazy eval status: UNIT/UNSAT
        # thereby keeping watched literals invariant for learnt clauses
        highest = None
        chosen_literal = None

        for literal in clause:
            if self.eval_literal(literal) == 0 and literal not in self.clause_literal_watchlist[clause]:
                if highest == None or highest < self.decision_levels[abs(literal)]:
                    highest = self.decision_levels[abs(literal)]
                    chosen_literal = literal

        self.add_watched_literal_ref(chosen_literal, clause)
        return chosen_literal

    def update_watched_literals(self, literal):
        """
        Called when a literal is assigned. Updates watched literals in clauses where the literal's value is 0.
            :param literal: Literal that has been assigned.
            :returns: None.
        """
        # removes all clauses watching literal where literal = 0
        literal = literal if self.eval_literal(literal) == 0 else -literal
        clauses = self.literal_clause_watchlist[literal][:]
        
        for clause in clauses:
            # no need to change reference since clause status will not change
            if self.eval_clause(clause) == UNSAT or self.eval_clause(clause) == SAT:
                continue

            self.remove_watched_literal_ref(literal, clause)
            new_literal = self.add_watched_literal(clause)

            # if new reference is assigned 0, then restore initial reference
            # keeps the invariants: 
            # 1. if watched literals eval to UNIT/UNSAT, all other literals in clause are 0
            # 2. UNSAT clause always watches last assigned variable
            if self.eval_literal(new_literal) == 0:
                self.remove_watched_literal_ref(new_literal, clause)
                self.add_watched_literal_ref(literal, clause)

    def initialize_learnt_clause(self, learnt_clause):
        # adds watched literals for learnt clause and keeps watched literals invariant
        self.add_watched_literal(learnt_clause)
        self.add_watched_literal(learnt_clause)

        if self.is_vsids:
            # increments vsids counter for all variables in clause
            for literal in learnt_clause:
                self.vsids_counter[abs(literal)] += 1
        
            # periodically, all counts are right binary shifted as per vsids heuristic
            self.vsids_countdown -= 1
            if self.vsids_countdown == 0:
                self.vsids_countdown = self.vsids_interval
                self.vsids_decay()
        
        # restarts search process by clearing all decisions and assignments made
        # does not delete clauses learnt thus far
        if self.is_restart:
            self.restart_countdown -= 1
            if self.restart_countdown <= 0:
                # the restart period is extended after each restart
                self.restart_countdown = self.restart_interval
                self.restart_interval *= self.restart_interval_multiplier
                self.restart()

    def vsids_decay(self):
        for variable in self.vsids_counter.keys():
            self.vsids_counter[variable] = self.vsids_counter[variable] >> 1

    def restart(self):
        self.trail = defaultdict(lambda: [], {})
        self.unassigned = [ i for i in range(1, self.n_vars + 1) ] # { variable }
        self.assignments = defaultdict(lambda: UNASSIGNED, {}) # { variable: value }
        self.antecedents = defaultdict(lambda: None, {}) # { variable: clause }
        self.decision_levels = defaultdict(lambda: 0, {}) # { variable: decision_level }
        self.decision_level = 0
        self.propagation_queue = []

    def track_clause(self, clause):
        # assigns a clause index to a clause
        self.clauses.append(clause)
        self.clause_index_map[clause] = len(self.clauses) - 1

    def add_resolution_to_proof(self, clause1, clause2, resolved_clause):
        self.track_clause(resolved_clause)

        resolution = (self.clause_index_map[clause1], 
                self.clause_index_map[clause2], 
                self.clause_index_map[resolved_clause])

        self.proof.append(resolution)

    def generate_proof(self):
        with open(self.output_path, "w") as f:
            f.write("v {}\n".format(len(self.clauses)))

            for clause in self.clauses:
                f.write(" ".join([ str(literal) for literal in clause ]) + "\n")
            
            for line in self.proof:
                f.write(" ".join([ str(clause_index) for clause_index in line ]) + "\n")

    def derive_empty_clause(self, formula, learnt_clause):
        # derives empty clause - used in proof of unsatisfiability
        self.restart() # restarts search process - clears search history

        # adds the learnt clause to the formula after backtracking
        formula.add(learnt_clause)
        self.initialize_learnt_clause(learnt_clause)

        # the conflict clause/learnt clause contains only the uip literal 
        # since there are no other decision levels with literals to contribute to the conflict
        unit_clause_1 = learnt_clause
        unit_literal = list(unit_clause_1)[0]
        assert len(learnt_clause) == 1

        # starts unit propagation from conflict clause
        self.propagation_queue.append((unit_literal, unit_clause_1))
        self.unit_propagation(formula)
        assert self.eval_formula(formula) == UNSAT

        # resolves all the way to the start of the implication graph to derive the empty clause
        empty_clause, stage = self.conflict_analysis(formula, is_first_uip=False)
        assert empty_clause == set()
