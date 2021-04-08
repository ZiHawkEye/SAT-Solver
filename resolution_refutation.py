"""
Defines SAT solver.
"""
from config import Config, PickBranchHeuristics, ConflictAnalysisHeuristics, VSIDSConfig
from notation import Formula, Clause, Literal
from enums import ENUM
from collections import deque
import sys
import random
import heapq

"""
    Antecedent clauses are the clauses that caused a literal to be implied / forced to become a single value.
    Example: f = (x_1 v x_2 v -x_3) ^ (x_4 v -x_5 v -x_6), then antecedent(x_1) = (x_1 v x_2 v -x_3) if and only if
    x_2 is assigned as 0 and x_3 is assigned as 1 (this causes x_1 to be implied to have a value of 1). We would only
    need to resolve all antecedent clauses recursively to obtain a new formula during conflict analysis
"""


class ClauseDatabase:
    def __init__(self, clauses):
        # clause map stores clauses -> its index and how it was derived (via resolution)
        # clause index map stores index -> clause mapping
        empty_clause = Clause.empty_clause()
        self.clause_map = {empty_clause: (-1, [])}
        self.clause_index_map = {-1: empty_clause}
        self.current_index = 0
        for clause in clauses:
            if clause not in self.clause_map:
                self.current_index += 1
                self.clause_map[clause] = (self.current_index, [])
                self.clause_index_map[self.current_index] = clause
        self.initial_num_unique_clauses = self.current_index

    """
        Inserts derived_clause into clause database and the resolution step that caused the derived_clause to be
        formed. c1 & c2 must exist in the database for this method to work correctly.
    """
    def insert_clause(self, c1, c2, derived_clause):
        if derived_clause not in self.clause_map:
            self.current_index += 1
            c1_index, c1_resolution = self.clause_map[c1]
            c2_index, c2_resolution = self.clause_map[c2]
            self.clause_map[derived_clause] = (self.current_index, [c1_index, c2_index])
            self.clause_index_map[self.current_index] = derived_clause

    def get_unit_clauses(self):
        result = []
        for cls, index_resolution_pair in self.clause_map.items():
            if len(cls.literals) == 1:
                result.append(cls)
        return result

    def get_clauses_that_lead_to_box(self):
        positive_unit_clause = None
        negative_unit_clause = None
        unit_clauses = self.get_unit_clauses()
        seen = {}
        for clause in unit_clauses:
            literal = list(clause.literals)[0]
            if literal.is_negated and literal.index in seen:
                negative_unit_clause = clause
                positive_unit_clause = seen[literal.index]
                break
            elif not literal.is_negated and -literal.index in seen:
                positive_unit_clause = clause
                negative_unit_clause = seen[-literal.index]
                break
            val = -literal.index if literal.is_negated else literal.index
            seen[val] = clause
        return positive_unit_clause, negative_unit_clause

    def get_resolution_refutation(self):
        pos_u_clause, neg_u_clause = self.get_clauses_that_lead_to_box()
        pos_u_clause_index, _ = self.clause_map[pos_u_clause]
        neg_u_clause_index, _ = self.clause_map[neg_u_clause]
        clause_trace = []
        index_trace = []
        # Run bfs backtracking
        queue = deque([pos_u_clause, neg_u_clause])
        visited = set() # Clause indices that have been visited
        while len(queue) > 0:
            curr_clause = queue.popleft()
            clause_index, resolution_clause_indices = self.clause_map[curr_clause]
            if clause_index in visited:
                continue
            visited.add(clause_index)
            if len(resolution_clause_indices) == 0:
                continue # Reached starting point
            c1_index, c2_index = resolution_clause_indices
            c1 = self.clause_index_map[c1_index]
            c2 = self.clause_index_map[c2_index]
            clause_trace.append((c1, c2, curr_clause))
            queue.append(c1)
            queue.append(c2)
        for c1, c2, c3 in clause_trace:
            c1_index, _ = self.clause_map[c1]
            c2_index, _ = self.clause_map[c2]
            c3_index, _ = self.clause_map[c3]
            index_trace.append((c1_index, c2_index, c3_index))
        sorted_index_trace = sorted(index_trace, key=lambda x: x[2])
        sorted_index_trace.append((pos_u_clause_index, neg_u_clause_index, -1)) # Resolution refutation.
        return sorted_index_trace


class ResolutionChecker:
    def __init__(self, trace, clause_db):
        self.trace = trace
        self.clause_db = clause_db

    def check(self):
        index_map = self.clause_db.clause_index_map
        correct = True
        for c1_index, c2_index, c3_index in self.trace:
            c1 = index_map[c1_index]
            c2 = index_map[c2_index]
            c3 = index_map[c3_index]
            c3_resolved = Clause.resolve(c1, c2)
            if c3 != c3_resolved:
                correct = False
                break
            print("Resolving({}, {}) gives {}".format(c1, c2, c3))
        return correct


class ResolutionRefutationSolver:
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
        # initialize db
        self.clause_db = ClauseDatabase(self.formula.clauses)

    def cdcl_solve(self):
        trail = []  # Additional stack to keep track of assignments and implication graph
        trail = self.initial_unit_propagate(self.formula, trail)
        self.decision_level += 1
        literal, value = self.vsids_pick_branch()  # Pick a literal and assign it a value
        trail.append((literal, value, None))  # Literal, Assigned Value and Antecedent Clause
        self.formula.set(literal, value)
        while True:
            trail = self.unit_propagate(self.formula, trail)
            if self.formula.evaluate_quick(trail) == ENUM.UNSAT:
                if self.decision_level == 0:
                    self.one_uip_conflict_analysis(self.formula, trail) # run one last conflict analysis
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
            else:
                if len(trail) == self.n_literals:
                    return self.formula.assignment, ENUM.SAT
                self.decision_level += 1
                literal, value = self.vsids_pick_branch()  # picks a literal and assign it a value
                trail.append((literal, value, None))  # Literal, Assigned Value and Antecedent Clause
                self.formula.set(literal, value)

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

    # Should just modify both assignment and trail directly
    def unit_propagate(self, formula, trail):
        self.num_of_unit_prop_calls += 1  # just to keep track and debug
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
        undecided_clauses = self.formula.find_all_undecided_clauses()  # list of clauses
        if len(undecided_clauses) == 0:  # Already satisfiable, can just assign the rest of the literals any value
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
            # Add into clause db
            derived_clause = Clause.resolve(conflict_clause, antecedent_clause)
            self.clause_db.insert_clause(conflict_clause, antecedent_clause, derived_clause)
            conflict_clause = derived_clause # update
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
        conflict_clause.adjust_watched_literals(self.formula.assignment, trail)
