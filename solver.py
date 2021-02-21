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
        self.backtrack_assignments = {
            0: {
                i: (ENUM.UNASSIGNED, self.decision_level) for i in range(1, n_literals + 1)
            }
        }
        # Since no assignments have been made, all the antecedent clauses at decision level 0 is empty
        self.backtrack_antecedent_clauses = {
            0: {
                i: [] for i in range(1, n_literals + 1)
            }
        }
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
        next_assignment, sat_status, next_antecedent_clauses = self.unit_propagate(self.formula,
                                                                                   self.backtrack_assignments[0],
                                                                                   self.backtrack_antecedent_clauses[0])
        if sat_status == ENUM.UNSAT:
            return next_assignment, ENUM.UNSAT

        iteration_count = 0
        while True:
            iteration_count += 1
            if iteration_count > 5:
                break
            next_unassigned_literal, value = self.pick_branch(self.formula, next_assignment)
            if next_unassigned_literal is None:
                break

            self.decision_level += 1

            # Copy from previous decision level
            next_antecedent_clauses = copy.deepcopy(self.backtrack_antecedent_clauses[self.decision_level - 1])
            next_assignment = self.backtrack_assignments[self.decision_level - 1].copy()
            print(next_assignment, "backtrack")
            next_assignment[next_unassigned_literal] = (value, self.decision_level)  # Assign it based it pick branch
            self.backtrack_antecedent_clauses[self.decision_level] = next_antecedent_clauses
            self.backtrack_assignments[self.decision_level] = next_assignment

            next_assignment, sat_status, next_antecedent_clauses = self.unit_propagate(self.formula,
                                                                                       next_assignment,
                                                                                       next_antecedent_clauses)
            if sat_status == ENUM.CONFLICT:
                backtrack_level = self.conflict_analysis(self.formula,
                                                         next_assignment,
                                                         next_antecedent_clauses)  # Updates clause by inserting clause that caused the conflict

                if backtrack_level < 0:
                    return next_assignment, ENUM.UNSAT
                else:
                    self.decision_level = backtrack_level  # Backtracking only needs to move to the backtrack level returned from conflict analysis

        # found a satisfying assignment
        return self.backtrack_assignments[self.decision_level], ENUM.SAT

    def get_next_unassigned_literal(self, assignment):
        for literal, assign in assignment.items():
            value, decision_level = assign
            if value == ENUM.UNASSIGNED:
                return literal
        return None

    def get_status(self, formula, assignment):
        return formula.evaluate(assignment)

    # Should just modify both assignment and antecedent_clauses directly
    def unit_propagate(self, formula, assignment, antecedent_clauses):
        self.num_of_unit_prop_calls += 1  # just to keep track and debug

        unit_clause, literal = formula.get_unit_clause_literal(assignment)
        while literal is not None:
            # update assignment
            antecedent_clauses[literal.literal].append(unit_clause)
            if literal.is_negated:
                assignment[literal.literal] = (
                    0, self.decision_level)  # Assign 0 to negated literal at this dl
            else:
                assignment[literal.literal] = (1, self.decision_level)  # Assign 1 to literal at this dl
            unit_clause, literal = formula.get_unit_clause_literal(assignment)
        sat_status = formula.evaluate(assignment)
        return assignment, sat_status, antecedent_clauses

    # todo pick literal and assign a value to it. - can try greedy
    def pick_branch(self, formula, assignment):
        literal = self.get_next_unassigned_literal(assignment)
        return literal, 1

    # todo should update formula with the clause that caused conflict
    def conflict_analysis(self, formula, conflicting_assignment, antecedent_clauses):
        print(conflicting_assignment)
        unsat_clause = formula.find_first_unsat_clause(conflicting_assignment)
        clauses_involved = {unsat_clause}
        clauses_to_resolve = [unsat_clause]
        '''for k,v in antecedent_clauses.items():
            print("{}: {}, ".format(k, [vv.to_string() for vv in v]), end='')
        print("")'''
        literals_involved = set([literal.literal for literal in unsat_clause.literals])
        literals_queue = [literal for literal in unsat_clause.literals]
        while len(literals_queue) > 0:
            literal = literals_queue.pop()
            conflicted_clauses = antecedent_clauses[literal.literal]
            for clause in conflicted_clauses:
                if clause not in clauses_involved:
                    clauses_involved.add(clause)
                    clauses_to_resolve.append(clause)
                    for l in clause.literals:
                        if l.literal not in literals_involved:
                            literals_involved.add(l.literal)
                            literals_queue.append(l)
        clauses_to_resolve.reverse()
        # print([c.to_string() for c in clauses_to_resolve])
        new_clause_to_add = clauses_to_resolve.pop()
        while len(clauses_to_resolve) > 0:
            new_clause_to_add = Clause.resolve(new_clause_to_add, clauses_to_resolve.pop())
        print(new_clause_to_add)
        formula.clauses.add(new_clause_to_add)  # Update formula directly
        assignments_that_caused_conflict = [conflicting_assignment[literal] for literal in literals_involved]
        backtrack_level = max([decision_level for assigned_value, decision_level in assignments_that_caused_conflict if decision_level < self.decision_level])
        return backtrack_level
