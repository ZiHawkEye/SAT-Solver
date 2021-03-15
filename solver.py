"""
Defines SAT solver.
"""
from config import Config, PickBranchHeuristics, ConflictAnalysisHeuristics
from notation import Formula, Clause, Literal
from enums import ENUM
import sys
import random
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

    def cdcl_solve(self):
        trail = []  # Additional stack to keep track of assignments and implication graph
        assignment = {i: ENUM.UNDECIDED for i in range(1, self.n_literals + 1)}  # Initially all unassigned
        while True:
            assignment, trail = self.unit_propagate(self.formula, assignment, trail)
            if self.formula.evaluate(assignment) == ENUM.UNSAT:
                if self.decision_level == 0:
                    return assignment, ENUM.UNSAT
                conflict_clause = self.one_uip_conflict_analysis(self.formula, assignment, trail)
                self.backtrack(conflict_clause, assignment, trail)  # Undo assignments
                self.formula.clauses.add(conflict_clause)

            else:
                if len(trail) == self.n_literals:
                    return assignment, ENUM.SAT
                self.decision_level += 1
                literal, value = self.pick_branch(self.formula, assignment)  # Pick a literal and assign it a value
                trail.append((literal, value, None))  # Literal, Assigned Value and Antecedent Clause
                assignment[literal] = value  # update assignment

    def get_next_unassigned_literal(self, assignment):
        for literal, value in assignment.items():
            if value == ENUM.UNASSIGNED:
                return literal
        return None

    def get_status(self, formula, assignment):
        return formula.evaluate(assignment)

    # Should just modify both assignment and trail directly
    def unit_propagate(self, formula, assignment, trail):
        self.num_of_unit_prop_calls += 1  # just to keep track and debug

        unit_clause, literal = formula.get_unit_clause_literal(assignment)
        while literal is not None:
            # update assignment
            if literal.is_negated:
                assignment[literal.index] = 0  # Assign 0 to negated literal
                trail.append((literal.index, 0, unit_clause))
            else:
                assignment[literal.index] = 1  # Assign 1 to literal
                trail.append((literal.index, 1, unit_clause))
            unit_clause, literal = formula.get_unit_clause_literal(assignment)
        return assignment, trail

    def pick_branch(self, formula, assignment):
        if Config.pick_branch_heuristic == PickBranchHeuristics.FIRST_VARIABLE:
            return self.pick_first_branch(formula, assignment)
        elif Config.pick_branch_heuristic == PickBranchHeuristics.RANDOM:
            return self.random_pick_branch(formula, assignment)
        elif Config.pick_branch_heuristic == PickBranchHeuristics.GREEDY:
            return self.greedy_pick_branch(formula, assignment)
        else:
            print("Pick branch variable not chosen. Terminating program...")
            sys.exit(1)

    def pick_first_branch(self, formula, assignment):
        literal = self.get_next_unassigned_literal(assignment)
        return literal, 1

    def random_pick_branch(self, formula, assignment):
        undecided_literals = []
        for literal, value in assignment.items():
            if value == ENUM.UNDECIDED:
                undecided_literals.append(literal)
        random_literal = random.choice(undecided_literals)
        random_value = random.choice([0, 1])
        return random_literal, random_value

    def greedy_pick_branch(self, formula, assignment):
        undecided_clauses = formula.find_all_undecided_clauses(assignment) # list of clauses
        if len(undecided_clauses) == 0: # Already satisfiable, can just assign the rest of the literals any value
            return self.pick_first_branch(formula, assignment)
        undecided_literals_dict = {literal: {0: 0, 1: 0} for
                                   literal, value in assignment.items() if value == ENUM.UNDECIDED}
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
        if Config.conflict_analysis_heuristic == ConflictAnalysisHeuristics.GRASP:
            return self.grasp_conflict_analysis(formula, conflicting_assignment, trail)
        elif Config.conflict_analysis_heuristic == ConflictAnalysisHeuristics.ONE_UIP:
            return self.one_uip_conflict_analysis(formula, conflicting_assignment, trail)
        else:
            print("Conflict analysis heuristic not selected. Terminating program...")
            sys.exit(1)

    # Grasp conflict analysis
    def grasp_conflict_analysis(self, formula, conflicting_assignment, trail):
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
        return new_clause_to_add

    # 1-UIP conflict analysis follow trail backwards
    def one_uip_conflict_analysis(self, formula, conflicting_assignment, trail):
        unsat_clause = formula.find_first_unsat_clause(conflicting_assignment)
        conflict_clause = unsat_clause

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
            num_of_implied_literals_at_this_level = len(
                [l for l in conflict_clause.literals if l.index in literals_at_this_level])
            if num_of_implied_literals_at_this_level == 1:
                # Reached 1-UIP point. This happens when the resolved clause has
                # only one literal decided at this decision level
                break
            literal, value, antecedent_clause = trail[i]
            i = i - 1
            if literal not in {l.index for l in conflict_clause.literals}:
                # Irrelevant literal - does not cause the conflict clause
                continue
            if antecedent_clause is None:
                continue
            conflict_clause = Clause.resolve(conflict_clause, antecedent_clause)
        return conflict_clause

    def backtrack(self, conflict_clause, assignment, trail):
        flag = False
        while len(trail) > 0:
            literal, value, antecedent = trail.pop()
            assignment[literal] = ENUM.UNASSIGNED
            for conflict_clause_literal in conflict_clause.literals:
                if literal == conflict_clause_literal.index:
                    flag = True

            if antecedent is None:
                self.decision_level = self.decision_level - 1
                if flag:
                    break
