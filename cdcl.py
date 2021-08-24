import sys
import argparse
import time

from formula2cnf import load_smtlib
from dpll import load_dimacs

parser = argparse.ArgumentParser()
parser.add_argument('infile', nargs='?', type=argparse.FileType('r', encoding='UTF-8'), default=sys.stdin)


class CDCL_solver:
    def __init__(self, clauses):
        self.unit_prop_counter = 0
        self.decisions_counter = 0
        self.checked_clauses_counter = 0

        self.reinitialize(clauses)

    def reinitialize(self, clauses):
        self.clauses = clauses      # list containing all clauses
        self.assignment = []        # queue containing assigned literals
        self.dec_levels = []        # similar queue but containing decision levels of corresponding assigned literals
        self.antecedents = dict()
        self.decision_level = 0
        self.conflicts_counter = 0

        self.watched_literals = dict()
        self.unit_literals = set()

        # watched literals initialization
        for i, clause in enumerate(clauses):
            for literal in clause:
                if literal not in self.watched_literals:
                    self.watched_literals[literal] = set()
                if -literal not in self.watched_literals:
                    self.watched_literals[-literal] = set()

        # watched literals setting & unit clauses finding
        for i, clause in enumerate(clauses):
            self.watched_literals[clause[0]].add(i)
            if len(clause) >= 2:
                self.watched_literals[clause[1]].add(i)
            elif len(clause) == 1:
                self.unit_literals.add(clause[0])

    def decide_literal(self):
        for literal in self.watched_literals.keys():
            if literal not in self.assignment and -literal not in self.assignment:
                self.decisions_counter += 1
                return literal
        return None

    def unit_propagation(self):
        """Returns conflict clause id or -1 if no conflict exists"""

        conflict_clause = -1
        while len(self.unit_literals) > 0:
            unit_literal = self.unit_literals.pop()
            conflict_clause, unit_literals = self.unit_propagate_literal(unit_literal)
            if conflict_clause >= 0:
                return conflict_clause
            else:
                self.unit_literals = self.unit_literals.union(unit_literals)

        return conflict_clause

    def unit_propagate_literal(self, literal):
        """Returns id of conflict clause (or -1) and a set of found unit literals"""

        self.unit_prop_counter += 1
        self.assignment.append(literal)
        self.dec_levels.append(self.decision_level)

        # trying to change watched literals in clauses where 'not literal' is watched
        found_unit_literals = set()
        not_longer_watched = list()
        conflict_clause = -1

        for clause_index in self.watched_literals[-literal]:
            self.checked_clauses_counter += 1
            next_watched_literal = None
            possible_unit_literal = None
            possible_unit_literal_satisfied = None

            if len(self.clauses[clause_index]) == 1:
                conflict_clause = clause_index
                continue

            neg_literal_offset = self.clauses[clause_index].index(-literal)
            for i in range(neg_literal_offset + 1, neg_literal_offset + len(self.clauses[clause_index])):
                l = self.clauses[clause_index][i % len(self.clauses[clause_index])]
                if clause_index in self.watched_literals[l]:
                    # 'l' is another watched literal in this clause
                    possible_unit_literal = l
                    if possible_unit_literal in self.assignment:
                        possible_unit_literal_satisfied = True
                    if -possible_unit_literal in self.assignment:
                        possible_unit_literal_satisfied = False
                else:
                    if not next_watched_literal and -l not in self.assignment:
                        next_watched_literal = l

            if next_watched_literal is None:
                # watched 'literal' cannot move in this clause
                if possible_unit_literal_satisfied is None:
                    found_unit_literals.add(possible_unit_literal)
                    self.antecedents[possible_unit_literal] = clause_index
                elif not possible_unit_literal_satisfied:
                    conflict_clause = clause_index
            else:
                not_longer_watched.append(clause_index)
                self.watched_literals[next_watched_literal].add(clause_index)

        for clause_index in not_longer_watched:
            self.watched_literals[-literal].remove(clause_index)

        return conflict_clause, found_unit_literals

    def conflict_analysis(self, conflict_clause_id):
        self.conflicts_counter += 1

        # searching for an assertive clause with 1-UIP
        C = set(self.clauses[conflict_clause_id])
        while True:
            literals_at_d_counter = 0
            latest_assignment_time = -1
            second_latest_ass_time = -1
            for literal in C:
                assignment_time = self.assignment.index(-literal)
                if self.dec_levels[assignment_time] == self.decision_level:
                    literals_at_d_counter += 1
                if assignment_time >= latest_assignment_time:
                    second_latest_ass_time = latest_assignment_time
                    latest_assignment_time = assignment_time
                elif assignment_time > second_latest_ass_time:
                    second_latest_ass_time = assignment_time

            if literals_at_d_counter <= 1:
                learned_clause = list(C)
                if len(learned_clause) == 1:
                    if self.decision_level == 0:
                        return -1, None, None
                    else:
                        return 0, learned_clause, learned_clause[0]
                else:
                    return self.dec_levels[second_latest_ass_time], learned_clause, -self.assignment[latest_assignment_time]

            resolved_literal = -self.assignment[latest_assignment_time]
            C.remove(resolved_literal)
            for literal in self.clauses[self.antecedents[-resolved_literal]]:
                if literal != -resolved_literal:
                    C.add(literal)

    def join_learned_clause(self, clause, unit_literal):
        new_clause_index = len(self.clauses)
        self.clauses.append(clause)
        self.watched_literals[unit_literal].add(new_clause_index)
        if len(clause) >= 2:
            if unit_literal != clause[0]:
                self.watched_literals[clause[0]].add(new_clause_index)
            else:
                self.watched_literals[clause[1]].add(new_clause_index)

        self.antecedents[unit_literal] = new_clause_index
        self.unit_literals = {unit_literal}

    def backtrack(self, backtrack_level):
        while len(self.assignment) > 0 and self.dec_levels[-1] > backtrack_level:
            self.assignment.pop()
            self.dec_levels.pop()
        self.decision_level = backtrack_level

    def try_to_solve(self):
        conflict_clause = self.unit_propagation()
        if conflict_clause >= 0:
            return None

        while True:
            current_literal = self.decide_literal()
            self.decision_level += 1

            if current_literal is None:
                # all variables assigned
                return self.assignment
            self.unit_literals = {current_literal}

            while True:
                conflict_clause = self.unit_propagation()
                if conflict_clause == -1:
                    break

                backtrack_level, learned_clause, new_unit_literal = self.conflict_analysis(conflict_clause)
                if backtrack_level == -1:
                    return None
                elif backtrack_level == -10:
                    return "restart"

                self.join_learned_clause(learned_clause, new_unit_literal)
                self.backtrack(backtrack_level)

    def solve(self):
        solution_found = False
        result = None
        while not solution_found:
            result = self.try_to_solve()
            if result is None or result != "restart":
                solution_found = True

        return result



if __name__ == "__main__":
    args = parser.parse_args()

    file_suffix = args.infile.name.split('.')[-1]

    if file_suffix == 'sat':
        clauses, variables_mapping = load_smtlib(args.infile)
    elif file_suffix == 'cnf':
        clauses = load_dimacs(args.infile)
    else:
        raise Exception("Unknown file type")

    solver = CDCL_solver(clauses)

    start = time.time()
    assignment = solver.solve()
    end = time.time()

    if assignment is None:
        print('UNSAT')
    else:
        print('SAT')
        print('satisfying assignment:')
        if file_suffix == 'cnf':
            print(sorted(assignment, key=abs))
        else:
            decoded_assignment_pos = [lit for lit, var in variables_mapping.items() if var in assignment]
            decoded_assignment_neg = ['-' + str(lit) for lit, var in variables_mapping.items() if -var in assignment]

            print(decoded_assignment_pos + decoded_assignment_neg)

    print()
    print('CPU time:', "{:.2f}".format(end - start))
    print('number of decisions:', solver.decisions_counter)
    print('number of steps of unit propagation:', solver.unit_prop_counter)
    print('total number of checked clauses:', solver.checked_clauses_counter)