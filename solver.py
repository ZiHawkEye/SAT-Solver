"""
Defines SAT solver.
"""
import copy
from notation import Formula, Clause, Literal
from enums import ENUM

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
        assignment = {i: ENUM.UNDECIDED for i in range(1, self.n_literals + 1)} # Initially all unassigned
        while True:
            assignment, trail = self.unit_propagate(self.formula, assignment, trail)
            if self.formula.evaluate(assignment) == ENUM.UNSAT:
                if self.decision_level == 0:
                    return assignment, ENUM.UNSAT
                conflict_clause = self.conflict_analysis(self.formula, assignment, trail)
                self.backtrack(conflict_clause, assignment, trail) # Undo assignments
                self.formula.clauses.add(conflict_clause)

            else:
                if len(trail) == self.n_literals:
                    return assignment, ENUM.SAT
                self.decision_level += 1
                literal, value = self.pick_branch(self.formula, assignment) # Pick a literal and assign it a value
                trail.append((literal, value, None)) # Literal, Assigned Value and Antecedent Clause
                assignment[literal] = value # update assignment

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
                assignment[literal.literal] = 0 # Assign 0 to negated literal
                trail.append((literal.literal, 0, unit_clause))
            else:
                assignment[literal.literal] = 1 # Assign 1 to literal
                trail.append((literal.literal, 1, unit_clause))
            unit_clause, literal = formula.get_unit_clause_literal(assignment)
        return assignment, trail

    # todo pick literal and assign a value to it. - can try greedy
    def pick_branch(self, formula, assignment):
        literal = self.get_next_unassigned_literal(assignment)
        return literal, 1

    def build_implication_graph(self, trail):
        graph = {}
        for literal, value, antecedent_clause in trail:
            graph[literal] = antecedent_clause
        return graph

    # todo should update formula with the clause that caused conflict
    def conflict_analysis(self, formula, conflicting_assignment, trail):
        implication_graph = self.build_implication_graph(trail)
        unsat_clause = formula.find_first_unsat_clause(conflicting_assignment)
        clauses_involved = {unsat_clause}
        clauses_to_resolve = [unsat_clause]
        literals_involved = set([literal.literal for literal in unsat_clause.literals])
        literals_queue = [literal for literal in unsat_clause.literals]
        while len(literals_queue) > 0:
            literal = literals_queue.pop()
            conflicted_clause = implication_graph[literal.literal]
            if conflicted_clause is not None:
                clauses_involved.add(conflicted_clause)
                clauses_to_resolve.append(conflicted_clause)
                for l in conflicted_clause.literals:
                    if l.literal not in literals_involved:
                        literals_involved.add(l.literal)
                        literals_queue.append(l)

        new_clause_to_add = Clause(set())
        for literal in literals_involved:
            if implication_graph[literal] is None: # UIP
                assigned_value = conflicting_assignment[literal]
                l = -Literal(str(literal)) if assigned_value == 1 else Literal(str(literal))
                new_clause_to_add.literals.add(l)
        # print("learnt clause: ", new_clause_to_add)
        return new_clause_to_add

    def backtrack(self, conflict_clause, assignment, trail):
        while len(trail) > 0:
            literal, value, antecedent = trail.pop()
            assignment[literal] = ENUM.UNASSIGNED
            for conflict_clause_literal in conflict_clause.literals:
                if literal == conflict_clause_literal.literal:
                    break
