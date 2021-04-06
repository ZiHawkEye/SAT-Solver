from enums import ENUM

"""
Defines notation classes.
"""


class Formula(object):
    def __init__(self, clauses, n_literals):
        self.clauses = clauses  # set of clauses
        self.n_literals = n_literals
        self.watch_list = {}
        self.initialize_watch_list()
        self.assignment = {i: ENUM.UNDECIDED for i in range(1, self.n_literals + 1)}  # Initially all unassigned

    def initialize_watch_list(self):
        for i in range(1, self.n_literals + 1):
            self.watch_list[Literal(str(i))] = set()
            self.watch_list[Literal(str(-i))] = set()
        for clause in self.clauses:
            for literal in clause.watched_literals:
                self.watch_list[literal].add(clause)

    def add_clause(self, clause):
        if clause not in self.clauses:
            self.clauses.add(clause)
            for literal in clause.watched_literals:
                self.watch_list[literal].add(clause)

    def to_string(self):
        formula_string = ", ".join([clause.to_string() for clause in self.clauses])
        return formula_string

    def __str__(self):
        return self.to_string()

    def __eq__(self, other):
        return isinstance(other, Formula) and self.clauses == other.clauses

    def set(self, literal_index, value):
        remove_from_watch_list = []
        add_to_watch_list = []
        falsified_literal = Literal(str(literal_index) if value == 0 else str(-literal_index))
        # self.verify_integrity_of_watch_list()
        self.assignment[literal_index] = value
        for clause in self.watch_list[falsified_literal]:
            if len(clause.watched_literals) < 2:
                continue
            else:
                # watch another literal
                first_wl, second_wl = clause.watched_literals
                next_unassigned_literal = None
                index = 0
                for j in range(len(clause.unwatched_literals)):
                    unwatched_literal = clause.unwatched_literals[j]
                    unwatched_status = unwatched_literal.evaluate(self.assignment)
                    if unwatched_status == ENUM.SAT or unwatched_status == ENUM.UNDECIDED:
                        next_unassigned_literal = unwatched_literal
                        index = j
                if first_wl == falsified_literal:
                    '''if second_wl.evaluate(self.assignment) == ENUM.SAT:
                        continue
                    elif second_wl.evaluate(self.assignment) == ENUM.UNSAT and next_unassigned_literal is None:
                        continue'''
                    # second_wl is undecided
                    # update first wl
                    if next_unassigned_literal is not None:
                        # swap
                        remove_from_watch_list.append(clause)
                        clause.watched_literals[0] = next_unassigned_literal
                        clause.unwatched_literals[index] = first_wl
                        add_to_watch_list.append((next_unassigned_literal, clause))
                else:
                    '''if first_wl.evaluate(self.assignment) == ENUM.SAT:
                        continue
                    elif first_wl.evaluate(self.assignment) == ENUM.UNSAT and next_unassigned_literal is None:
                        continue'''
                    # first_wl is undecided
                    # update second wl
                    if next_unassigned_literal is not None:
                        # swap
                        remove_from_watch_list.append(clause)
                        clause.watched_literals[1] = next_unassigned_literal
                        clause.unwatched_literals[index] = second_wl
                        add_to_watch_list.append((next_unassigned_literal, clause))
        for clause_to_remove in remove_from_watch_list:
            self.watch_list[falsified_literal].remove(clause_to_remove)
        for literal_to_add, clause_to_add in add_to_watch_list:
            self.watch_list[literal_to_add].add(clause_to_add)

    def unset(self, literal_index):
        self.assignment[literal_index] = ENUM.UNDECIDED

    def verify_integrity_of_watch_list(self):
        if self.evaluate() == ENUM.UNSAT:
            return
        for literal, watched_clauses in self.watch_list.items():
            for clause in watched_clauses:
                if len(clause.watched_literals) < 2:
                    status = literal.evaluate(self.assignment)
                    if status == ENUM.SAT or status == ENUM.UNDECIDED:
                        # ok
                        continue
                else:
                    first_wl, second_wl = clause.watched_literals
                    first_status = first_wl.evaluate(self.assignment)
                    second_status = second_wl.evaluate(self.assignment)
                    if first_status == ENUM.UNSAT and second_status == ENUM.UNSAT:
                        unwatched_status = max([e.evaluate(self.assignment) for e in clause.unwatched_literals] + [0])
                        if unwatched_status != ENUM.UNSAT:
                            print("violated invariant")
                    if first_status == ENUM.UNSAT or second_status == ENUM.UNSAT:
                        unwatched_status = max([e.evaluate(self.assignment) for e in clause.unwatched_literals] + [0])
                        if unwatched_status != ENUM.UNSAT:
                            print("violation {}".format(str(clause)))

    def evaluate(self):
        value = min([clause.evaluate(self.assignment) for clause in self.clauses])
        return value

    def evaluate_assignment(self, assignment):
        return min([max([lit.evaluate(assignment) for lit in clause.literals]) for clause in self.clauses])

    def evaluate_quick(self, trail):
        trail_len = len(trail)
        for literal, value, antecedent_clause in trail:
            falsified_literal = Literal(str(literal) if value == 0 else str(-literal))
            for clause in self.watch_list[falsified_literal]:
                lazy_clause_status = max([l.evaluate(self.assignment) for l in clause.watched_literals])
                if lazy_clause_status == ENUM.UNSAT:
                    return ENUM.UNSAT
        if trail_len < self.n_literals:
            return ENUM.UNDECIDED
        else:
            return ENUM.SAT

    '''def get_unit_clause_literal(self, assignment, trail):
        # return self.get_unit_clause_literal_slowly(assignment)
        if len(trail) == 0:
            return self.get_unit_clause_literal_slowly(assignment)
        else:
            return self.get_unit_clause_literal_lazily(assignment, trail)'''

    # todo take into account recently added conflict clause to look for unit clause literals
    def get_unit_clause_literal_lazily(self, assignment, trail, conflict_clause=None):
        if len(trail) == 0:
            return self.get_unit_clause_literal_slowly(assignment)
        unit_clause = None
        literal = None
        remove_from_watch_list = []
        add_to_watch_list = []
        if conflict_clause is not None:
            for literal in conflict_clause.literals:
                if literal.evaluate(assignment) == ENUM.UNASSIGNED:
                    return conflict_clause, literal
        else:
            previous_literal, value, antecedent_clause = trail[-1]
            falsified_literal = Literal(str(previous_literal) if value == 0 else str(-previous_literal))
            for clause in self.watch_list[falsified_literal]:
                if len(clause.watched_literals) < 2:
                    return None, None   # This clause is falsified
                else:
                    # watch another literal
                    first_wl, second_wl = clause.watched_literals
                    next_unassigned_literal = None
                    index = 0
                    already_sat = False
                    for j in range(len(clause.unwatched_literals)):
                        unwatched_literal = clause.unwatched_literals[j]
                        unwatched_status = unwatched_literal.evaluate(assignment)
                        if unwatched_status == ENUM.SAT:
                            already_sat = True
                        elif unwatched_status == ENUM.UNDECIDED:
                            next_unassigned_literal = unwatched_literal
                            index = j
                    if already_sat:
                        continue
                    if first_wl == falsified_literal:
                        if second_wl.evaluate(assignment) == ENUM.SAT:
                            continue
                        elif second_wl.evaluate(assignment) == ENUM.UNSAT:
                            return None, None
                        # second_wl is undecided
                        # update first wl
                        if next_unassigned_literal is not None:
                            # swap
                            remove_from_watch_list.append(clause)
                            clause.watched_literals[0] = next_unassigned_literal
                            clause.unwatched_literals[index] = first_wl
                            add_to_watch_list.append((next_unassigned_literal, clause))
                        else:
                            # no unassigned next literal, second_wl forms the unit clause
                            unit_clause = clause
                            literal = second_wl
                    else:
                        if first_wl.evaluate(assignment) == ENUM.SAT:
                            continue
                        elif first_wl.evaluate(assignment) == ENUM.UNSAT:
                            return None, None
                        # first_wl is undecided
                        # update second wl
                        if next_unassigned_literal is not None:
                            # swap
                            remove_from_watch_list.append(clause)
                            clause.watched_literals[1] = next_unassigned_literal
                            clause.unwatched_literals[index] = second_wl
                            add_to_watch_list.append((next_unassigned_literal, clause))
                        else:
                            # no unassigned next literal, first_wl forms the unit clause
                            unit_clause = clause
                            literal = first_wl
            for clause_to_remove in remove_from_watch_list:
                self.watch_list[falsified_literal].remove(clause_to_remove)
            for literal_to_add, clause_to_add in add_to_watch_list:
                self.watch_list[literal_to_add].add(clause_to_add)
            return unit_clause, literal

    def get_unit_clause_literal_lazily_2(self, trail):
        if self.evaluate_quick(trail) == ENUM.UNSAT:
            return None, None
        for i in range(len(trail) - 1, -1, -1):
            literal, value, antecedent_clause = trail[i]
            falsified_literal = Literal(str(literal) if value == 0 else str(-literal))
            for clause in self.watch_list[falsified_literal]:
                if len(clause.watched_literals) <= 1:
                    return clause, clause.watched_literals[0]
                else:
                    first_wl, second_wl = clause.watched_literals
                    first_status = first_wl.evaluate(self.assignment)
                    second_status = second_wl.evaluate(self.assignment)
                    if first_status == ENUM.SAT or second_status == ENUM.SAT:
                        continue
                    elif first_status == ENUM.UNSAT or second_status == ENUM.UNSAT:
                        if first_status == ENUM.UNSAT:
                            return clause, second_wl
                        else:
                            return clause, first_wl
            if antecedent_clause is None:
                break
        return None, None

    def get_unit_clause_literal_lazily_3(self, trail, start_index):
        if self.evaluate_quick(trail) == ENUM.UNSAT:
            return None, None
        for i in range(start_index, len(trail)):
            literal, value, antecedent_clause = trail[i]
            falsified_literal = Literal(str(literal) if value == 0 else str(-literal))
            for clause in self.watch_list[falsified_literal]:
                if len(clause.watched_literals) <= 1:
                    return clause, clause.watched_literals[0]
                else:
                    first_wl, second_wl = clause.watched_literals
                    first_status = first_wl.evaluate(self.assignment)
                    second_status = second_wl.evaluate(self.assignment)
                    if first_status == ENUM.SAT or second_status == ENUM.SAT:
                        continue
                    elif first_status == ENUM.UNSAT or second_status == ENUM.UNSAT:
                        if first_status == ENUM.UNSAT:
                            return clause, second_wl
                        else:
                            return clause, first_wl
            if antecedent_clause is None:
                break
        return None, None

    def get_unit_clause_literal_slowly(self, trail):
        unit_clause = None
        literal = None
        if self.evaluate() == ENUM.CONFLICT:
            return unit_clause, literal
        for clause in self.clauses:
            literal_list = list(clause.literals)
            statuses = [literal.evaluate(self.assignment) for literal in literal_list]
            status = max(statuses)
            undecided_literals_index = [index for index, value in enumerate(statuses) if value == ENUM.UNDECIDED]
            if status == ENUM.SAT:
                continue  # This clause has been satisfied
            if status == ENUM.UNSAT:
                break  # This clause is unsatisfied, can break early
            if len(undecided_literals_index) == 1:
                unit_clause = clause
                literal = literal_list[undecided_literals_index[0]]
                break
        return unit_clause, literal

    def get_unit_clause_literal_slowly_2(self, trail):
        unit_clause = None
        literal = None
        for wl, watched_clauses in self.watch_list.items():
            for watched_clause in watched_clauses:
                if len(watched_clause.watched_literals) == 1:
                    if wl.evaluate(self.assignment) == ENUM.UNDECIDED:
                        unit_clause = watched_clause
                        literal = wl
                else:
                    first_wl, second_wl = watched_clause.watched_literals
                    first_status = first_wl.evaluate(self.assignment)
                    second_status = second_wl.evaluate(self.assignment)
                    if first_status == ENUM.SAT or second_status == ENUM.SAT:
                        continue
                    elif first_status == ENUM.UNSAT and second_status == ENUM.UNSAT:
                        return None, None
                    elif first_status == ENUM.UNDECIDED and second_status == ENUM.UNDECIDED:
                        continue
                    else:
                        # unit clause
                        unit_clause = watched_clause
                        if first_status == ENUM.UNDECIDED:
                            literal = first_wl
                        else:
                            literal = second_wl
        return unit_clause, literal

    def find_first_unsat_clause(self, trail):
        for i in range(len(trail) - 1, -1, -1):
            literal, value, antecedent_clause = trail[i]
            falsified_literal = Literal(str(literal) if value == 0 else str(-literal))
            for clause in self.watch_list[falsified_literal]:
                if clause.evaluate(self.assignment) == ENUM.UNSAT:
                    return clause
        '''for clause in self.clauses:
            if clause.evaluate(self.assignment) == ENUM.UNSAT:
                return clause'''
        return None

    def find_all_undecided_clauses(self):
        undecided_clauses = []
        for clause in self.clauses:
            if clause.evaluate(self.assignment) == ENUM.UNDECIDED:
                undecided_clauses.append(clause)
        return undecided_clauses


class Clause(object):
    def __init__(self, literals):
        self.literals = frozenset(literals)  # set of literals
        literal_list = list(literals)
        self.watched_literals = literal_list[0:2]   # pick the first two literals to be watched
        self.unwatched_literals = literal_list[2:]  # remaining

    def to_string(self):
        return "(" + ", ".join([literal.to_string() for literal in self.literals]) + ")"

    def __str__(self):
        return self.to_string()

    def __hash__(self):
        return hash(self.literals)

    def __eq__(self, other):
        return isinstance(other, Clause) and self.literals == other.literals

    def evaluate(self, assignment):
        if len(self.literals) == 0:
            return 0
        statuses = [literal.evaluate(assignment) for literal in self.watched_literals]
        return max(statuses)

    def adjust_watched_literals(self, assignment, trail):
        # adjust the clause's watched literals
        literal_list = list(self.literals)
        self.watched_literals = []
        self.unwatched_literals = []
        for literal in literal_list:
            if len(self.watched_literals) == 2:
                self.unwatched_literals.append(literal)
            else:
                status = literal.evaluate(assignment)
                if status == ENUM.UNDECIDED or status == ENUM.SAT:
                    self.watched_literals.append(literal)
                else:
                    self.unwatched_literals.append(literal)
        if len(literal_list) > 1 and len(self.watched_literals) < 2:
            # print([str(l) for l in self.watched_literals], [str(p) for p in self.unwatched_literals])
            # bring the most recent unwatched literal to watch list
            for j in range(len(trail) - 1, -1, -1):
                literal_index, value, antecedent_clause = trail[j]
                for uw_l in self.unwatched_literals:
                    if uw_l.index == literal_index:
                        # print(uw_l.index, literal_index)
                        self.watched_literals.append(uw_l)
                        self.unwatched_literals.remove(uw_l)
                        # print([str(l) for l in self.watched_literals], [str(p) for p in self.unwatched_literals])
                        return



    def remove_trivial_literals(self):
        updated_literal_set = set()
        for literal in self.literals:
            if -literal not in self.literals:
                updated_literal_set.add(literal)
        self.literals = updated_literal_set

    @staticmethod
    def resolve(clause1, clause2):
        literals = set()
        for literal in clause1.literals:
            if -literal not in clause2.literals:
                literals.add(literal)

        for literal in clause2.literals:
            if -literal not in clause1.literals:
                literals.add(literal)
        return Clause(literals)


class Literal(object):
    def __init__(self, dimacs_literal_format):
        literal = int(dimacs_literal_format)
        self.index = abs(literal)
        self.is_negated = literal < 0

    def to_string(self):
        return str(-1 * self.index) if self.is_negated else str(self.index)

    def __str__(self):
        return str(-1 * self.index) if self.is_negated else str(self.index)

    def __hash__(self):
        return hash(self.to_string())

    def __eq__(self, other):
        return isinstance(other, Literal) and self.index == other.index and self.is_negated == other.is_negated

    def __neg__(self):
        string_form = self.to_string()
        negated_string_form = str(int(string_form) * -1)
        return Literal(negated_string_form)

    def evaluate(self, assignment):
        value = assignment[self.index]
        if self.is_negated:
            return 1 - value
        else:
            return value

    def evaluate_by_value(self, value):
        if self.is_negated:
            return 1 - value
        else:
            return value
