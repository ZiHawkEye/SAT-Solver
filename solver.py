"""
Defines SAT solver.
"""
from config import Config, PickBranchHeuristics, ConflictAnalysisHeuristics, VSIDSConfig
from notation import Formula, Clause, Literal
from enums import ENUM
import sys
import random
import heapq
"""
    Antecedent clauses are the clauses that caused a literal to be implied / forced to become a single value.
    Example: f = (x_1 v x_2 v -x_3) ^ (x_4 v -x_5 v -x_6), then antecedent(x_1) = (x_1 v x_2 v -x_3) if and only if
    x_2 is assigned as 0 and x_3 is assigned as 1 (this causes x_1 to be implied to have a value of 1). We would only
    need to resolve all antecedent clauses recursively to obtain a new formula during conflict analysis
"""


class Solver:
    def __init__(self, formula, n_literals):
        self.n_literals = n_literals
        self.formula = formula
        self.decision_level = 0
        self.num_of_unit_prop_calls = 0
        self.variable_scores = {i: 0 for i in range(1, n_literals + 1)}
        self.conflict_count = 0
        for clause in self.formula.clauses:
            for literal in clause.literals:
                self.variable_scores[literal.index] += 1

    '''
    def dpll_solve(self):
        return self.dpll_recursion(self.formula, self.assignments)

    def dpll_recursion(self, formula, assignment):
        updated_assignment = self.unit_propagate(formula, assignment)
        status = self.get_status(formula, updated_assignment)
        if status == ENUM.SAT:
            return updated_assignment, ENUM.SAT
        elif status == ENUM.CONFLICT:
            return updated_assignment, ENUM.UNSAT
        else: # Undecided
            next_literal = self.get_next_unassigned_literal(updated_assignment)
            updated_assignment[next_literal] = 0 # Set to 0 first
            
            recursed_assignment, sat_result = self.dpll_recursion(formula, updated_assignment)
            if sat_result == ENUM.UNSAT:
                updated_assignment[next_literal] = 1 # Set to 1 next
                return self.dpll_recursion(formula, updated_assignment)
            else:
                return recursed_assignment, ENUM.SAT
    '''

    def cdcl_solve(self):
        trail = []  # Additional stack to keep track of assignments and implication graph
        trail = self.initial_unit_propagate(self.formula, trail)
        c = None
        self.decision_level += 1
        literal, value = self.pick_branch()  # Pick a literal and assign it a value
        trail.append((literal, value, None))  # Literal, Assigned Value and Antecedent Clause
        self.formula.set(literal, value)
        while True:
            trail = self.unit_propagate_2(self.formula, trail, c)
            if self.formula.evaluate_quick(trail) == ENUM.UNSAT:
                if self.decision_level == 0:
                    return self.formula.assignment, ENUM.UNSAT
                conflict_clause, most_recent_dl_lt = self.one_uip_conflict_analysis(self.formula, trail)
                self.backtrack(conflict_clause, trail, most_recent_dl_lt)  # Undo assignments
                # update variable records & decay if required
                self.conflict_count += 1
                if self.conflict_count >= VSIDSConfig.DECAY_TIME:
                    self.conflict_count = 0
                    for i in range(1, self.n_literals + 1):
                        self.variable_scores[i] = self.variable_scores[i] / VSIDSConfig.MULTIPLICATIVE_DECAY_FACTOR
                for var in conflict_clause.literals:
                    self.variable_scores[var.index] += VSIDSConfig.CONFLICT_BUMP
                self.formula.add_clause(conflict_clause)
                if len(conflict_clause.literals) == 1:
                    unit_clause_literal = list(conflict_clause.literals)[0]
                    if unit_clause_literal.is_negated:
                        self.formula.set(unit_clause_literal.index, 0)
                        trail.append((unit_clause_literal.index, 0, conflict_clause))
                    else:
                        self.formula.set(unit_clause_literal.index, 1)
                        trail.append((unit_clause_literal.index, 1, conflict_clause))
                c = conflict_clause
            else:
                if len(trail) == self.n_literals:
                    return self.formula.assignment, ENUM.SAT
                self.decision_level += 1
                literal, value = self.pick_branch()  # Pick a literal and assign it a value
                trail.append((literal, value, None))  # Literal, Assigned Value and Antecedent Clause
                # print(trail)
                self.formula.set(literal, value)
                c = None

    def get_next_unassigned_literal(self):
        for literal, value in self.formula.assignment.items():
            if value == ENUM.UNASSIGNED:
                return literal
        return None

    def get_status(self):
        return self.formula.evaluate()

    # Initial unit propagate
    def initial_unit_propagate(self, formula, trail):
        self.num_of_unit_prop_calls += 1  # just to keep track and debug
        for wl, watched_clauses in self.formula.watch_list.items():
            for clause in watched_clauses:
                if len(clause.literals) == 1:
                    literal = list(clause.literals)[0]
                    if literal.is_negated:
                        trail.append((literal.index, 0, clause))
                    else:
                        trail.append((literal.index, 1, clause))
        for literal_index, value, clause in trail:
            self.formula.set(literal_index, value)
        start = 0
        while start < len(trail):
            while True:
                unit_clause, literal = formula.get_unit_clause_literal_lazily_3(trail, start)
                if unit_clause is None:
                    break
                # update assignment
                if literal.is_negated:
                    self.formula.set(literal.index, 0)  # Assign 0 to negated literal
                    trail.append((literal.index, 0, unit_clause))
                else:
                    self.formula.set(literal.index, 1)  # Assign 1 to literal
                    trail.append((literal.index, 1, unit_clause))
            start += 1
        return trail

    def initial_unit_propagate_2(self, formula, trail):
        self.num_of_unit_prop_calls += 1  # just to keep track and debug
        unit_clause, literal = formula.get_unit_clause_literal_slowly_2(trail)
        while literal is not None:
            # update assignment
            if literal.is_negated:
                self.formula.set(literal.index, 0)  # Assign 0 to negated literal
                trail.append((literal.index, 0, unit_clause))
            else:
                self.formula.set(literal.index, 1)  # Assign 1 to literal
                trail.append((literal.index, 1, unit_clause))
            # print(trail)
            unit_clause, literal = formula.get_unit_clause_literal_slowly_2(trail)
        return trail

    # Should just modify both assignment and trail directly
    def unit_propagate(self, formula, trail, conf):
        self.num_of_unit_prop_calls += 1  # just to keep track and debug
        unit_clause, literal = formula.get_unit_clause_literal_slowly_2(trail)
        while literal is not None:
            # update assignment
            if literal.is_negated:
                self.formula.set(literal.index, 0)  # Assign 0 to negated literal
                trail.append((literal.index, 0, unit_clause))
            else:
                self.formula.set(literal.index, 1)  # Assign 1 to literal
                trail.append((literal.index, 1, unit_clause))
            # print(trail)
            unit_clause, literal = formula.get_unit_clause_literal_lazily_2(trail)
        return trail

    def unit_propagate_2(self, formula, trail, conf):
        self.num_of_unit_prop_calls += 1  # just to keep track and debug
        unit_clause = None
        literal = None
        start = len(trail) - 1
        while start >= 0:
            lt, v, cls = trail[start]
            if cls is None:
                break
            start -= 1
        if start == -1:
            start = 0
        while start < len(trail):
            while True:
                unit_clause, literal = formula.get_unit_clause_literal_lazily_3(trail, start)
                if unit_clause is None:
                    break
                if literal.is_negated:
                    self.formula.set(literal.index, 0)  # Assign 0 to negated literal
                    trail.append((literal.index, 0, unit_clause))
                else:
                    self.formula.set(literal.index, 1)  # Assign 1 to literal
                    trail.append((literal.index, 1, unit_clause))
            start += 1
        return trail

    # todo pick literal and assign a value to it. - can try greedy
    def pick_branch(self):
        if Config.pick_branch_heuristic == PickBranchHeuristics.VSIDS:
            return self.vsids_pick_branch()
        elif Config.pick_branch_heuristic == PickBranchHeuristics.FIRST_VARIABLE:
            return self.pick_first_branch()
        elif Config.pick_branch_heuristic == PickBranchHeuristics.RANDOM:
            return self.random_pick_branch()
        elif Config.pick_branch_heuristic == PickBranchHeuristics.GREEDY:
            return self.greedy_pick_branch()
        else:
            print("Pick branch variable not chosen. Terminating program...")
            sys.exit(1)

    def vsids_pick_branch(self):
        pq = [(-v, k) for k, v in self.variable_scores.items()]
        heapq.heapify(pq)
        while len(pq) > 0:
            score, var = heapq.heappop(pq)
            if self.formula.assignment[var] == ENUM.UNDECIDED:
                return var, random.choice([0, 1])
        return None, None

    def pick_first_branch(self):
        literal = self.get_next_unassigned_literal()
        return literal, 1

    def random_pick_branch(self):
        undecided_literals = []
        for literal, value in self.formula.assignment.items():
            if value == ENUM.UNDECIDED:
                undecided_literals.append(literal)
        random_literal = random.choice(undecided_literals)
        random_value = random.choice([0, 1])
        return random_literal, random_value

    def greedy_pick_branch(self):
        undecided_clauses = self.formula.find_all_undecided_clauses() # list of clauses
        if len(undecided_clauses) == 0: # Already satisfiable, can just assign the rest of the literals any value
            return self.pick_first_branch()
        undecided_literals_dict = {literal: {0: 0, 1: 0} for
                                   literal, value in self.formula.assignment.items() if value == ENUM.UNDECIDED}
        for clause in undecided_clauses:
            for literal in clause.literals:
                if literal.index in undecided_literals_dict:
                    if literal.is_negated:
                        undecided_literals_dict[literal.index][0] += 1
                    else:
                        undecided_literals_dict[literal.index][1] += 1
        literal_that_will_satisfy_largest_num_of_clauses = None
        num_of_clauses_that_will_be_satisfied = 0
        value = 0
        for literal, sign_counts in undecided_literals_dict.items():
            if sign_counts[0] < sign_counts[1]:
                if sign_counts[1] > num_of_clauses_that_will_be_satisfied:
                    num_of_clauses_that_will_be_satisfied = sign_counts[1]
                    literal_that_will_satisfy_largest_num_of_clauses = literal
                    value = 1
            else:
                if sign_counts[0] > num_of_clauses_that_will_be_satisfied:
                    num_of_clauses_that_will_be_satisfied = sign_counts[0]
                    literal_that_will_satisfy_largest_num_of_clauses = literal
                    value = 0
        return literal_that_will_satisfy_largest_num_of_clauses, value

    def build_implication_graph(self, trail):
        graph = {}
        for literal, value, antecedent_clause in trail:
            graph[literal] = antecedent_clause
        return graph

    # proxy function
    def conflict_analysis(self, formula, conflicting_assignment, trail):
        if Config.conflict_analysis_heuristic == ConflictAnalysisHeuristics.ONE_UIP:
            return self.one_uip_conflict_analysis(formula, trail)
        elif Config.conflict_analysis_heuristic == ConflictAnalysisHeuristics.GRASP:
            return self.grasp_conflict_analysis(formula, conflicting_assignment, trail)
        else:
            print("Conflict analysis heuristic not selected. Terminating program...")
            sys.exit(1)

    # Grasp conflict analysis
    '''def grasp_conflict_analysis(self, formula, conflicting_assignment, trail):
        implication_graph = self.build_implication_graph(trail)
        unsat_clause = formula.find_first_unsat_clause(conflicting_assignment)
        clauses_involved = {unsat_clause}
        clauses_to_resolve = [unsat_clause]
        literals_involved = set([literal.index for literal in unsat_clause.literals])
        literals_queue = [literal for literal in unsat_clause.literals]
        while len(literals_queue) > 0:
            literal = literals_queue.pop()
            conflicted_clause = implication_graph[literal.index]
            if conflicted_clause is not None:
                clauses_involved.add(conflicted_clause)
                clauses_to_resolve.append(conflicted_clause)
                for l in conflicted_clause.literals:
                    if l.index not in literals_involved:
                        literals_involved.add(l.index)
                        literals_queue.append(l)

        new_clause_to_add = Clause(set())
        for literal in literals_involved:
            if implication_graph[literal] is None:  # UIP
                assigned_value = conflicting_assignment[literal]
                l = -Literal(str(literal)) if assigned_value == 1 else Literal(str(literal))
                new_clause_to_add.literals.add(l)
        # print("learnt clause: ", new_clause_to_add)
        return new_clause_to_add'''

    # 1-UIP conflict analysis follow trail backwards
    def one_uip_conflict_analysis(self, formula, trail):
        unsat_clause = formula.find_first_unsat_clause(trail)
        conflict_clause = unsat_clause
        most_recent_dl_literal_index = None
        literals_at_this_level = set()
        i = len(trail) - 1
        # First pass to get all literals at this level
        while i >= 0:
            literal, value, antecedent_clause = trail[i]
            literals_at_this_level.add(literal)
            i = i - 1
            if antecedent_clause is None:
                break

        # Second pass to resolve clauses backward with respect to trail
        i = len(trail) - 1
        while i >= 0:
            implied_literals_at_this_level = [lt.index for lt in conflict_clause.literals
                                              if lt.index in literals_at_this_level]
            if len(implied_literals_at_this_level) == 1:
                # Reached 1-UIP point. This happens when the resolved clause has
                # only one literal decided at this decision level
                most_recent_dl_literal_index = implied_literals_at_this_level[0]
                break
            literal, value, antecedent_clause = trail[i]
            i = i - 1
            if literal not in {l.index for l in conflict_clause.literals}:
                # Irrelevant literal - does not cause the conflict clause
                continue
            if antecedent_clause is None:
                continue
            conflict_clause = Clause.resolve(conflict_clause, antecedent_clause)
        return conflict_clause, most_recent_dl_literal_index

    def backtrack(self, conflict_clause, trail, most_recent_dl_literal_index):
        literals_to_consider = [lit.index for lit in conflict_clause.literals]
        literals_to_consider.remove(most_recent_dl_literal_index)
        i = len(trail) - 1
        stopping_literal = None
        while i > 0:
            literal, value, antecedent_clause = trail[i]
            if literal in literals_to_consider:
                break
            i = i - 1
        while i < len(trail) - 1:
            i = i + 1
            literal, value, antecedent_clause = trail[i]
            if antecedent_clause is None:
                stopping_literal = literal
                break
        while len(trail) > 0:
            literal, value, antecedent_clause = trail.pop()
            self.formula.unset(literal)
            if antecedent_clause is None:
                self.decision_level -= 1
            if literal == stopping_literal:
                break
        """flag = False
        while len(trail) > 0:
            literal, value, antecedent = trail.pop()
            self.formula.unset(literal)
            for conflict_clause_literal in conflict_clause.literals:
                if literal == conflict_clause_literal.index and (
                        literal != most_recent_dl_literal_index or len(conflict_clause.literals) == 1):
                    flag = True
            if antecedent is None:
                self.decision_level = self.decision_level - 1
                if flag:
                    break"""
        conflict_clause.adjust_watched_literals(self.formula.assignment, trail)
