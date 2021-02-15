"""
Defines SAT solver.
"""
import copy
from notation import Formula
from enums import ENUM

class Solver:
    def __init__(self, formula, n_literals):
        self.n_literals = n_literals
        self.formula = formula
        self.decision_level = 0
        self.assignments = { i: ENUM.UNASSIGNED for i in range(1, n_literals + 1) } # keeps track of assignments at each decision level.
        self.num_of_unit_prop_calls = 0

    def dpll_solve(self):
        return self.dpll_recursion(self.formula, self.assignments)

    def dpll_recursion(self, formula, assignment):
        '''
        Solve using DPLL. Useful to test unit propagation.
        '''
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

    def get_next_unassigned_literal(self, assignment):
        for literal, assigned_value in assignment.items():
            if assigned_value == ENUM.UNASSIGNED:
                return literal
        return None
    
    def get_status(self, formula, assignment):
        return formula.evaluate(assignment)

    def unit_propagate(self, formula, assignment):
        self.num_of_unit_prop_calls += 1
        
        updated_assignment = assignment.copy()
        unit_clause_literal = formula.get_unit_clause_literal(updated_assignment)
        while (unit_clause_literal != None):
            # update assignment
            if unit_clause_literal.is_negated:
                updated_assignment[unit_clause_literal.literal] = 0 # Assign 0 to negated literal
            else:
                updated_assignment[unit_clause_literal.literal] = 1 # Assign 1 to literal
            unit_clause_literal = formula.get_unit_clause_literal(updated_assignment)
        return updated_assignment
