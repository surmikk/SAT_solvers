import sys
import argparse
import time
import math
import random

from formula2cnf import load_smtlib
from dpll import load_dimacs

parser = argparse.ArgumentParser()
parser.add_argument('infile', nargs='?', type=argparse.FileType('r', encoding='UTF-8'), default=sys.stdin)
parser.add_argument('--restart', choices=['geometric', 'Luby'], default=None)
parser.add_argument('--deletion', choices=['short', 'active', 'LBD'], default=None)
parser.add_argument('--decision', choices=['random', 'most_common'], default='random')

random.seed(42)


class Luby:
    def __init__(self):
        self.constant = 100
        self.history = []
        self.i = -1
        self.get_next()     # auxiliary step for skipping the first element (1/2)

    def get_next(self):
        self.i += 1

        k = math.log2(self.i + 1)
        if k.is_integer():
            self.history.append(int(2**(k-1)))
        else:
            k = int(math.log2(self.i)) + 1
            self.history.append(
                self.history[self.i - 2**(k-1) + 1]
            )
        return self.history[-1]


class CDCL_solver:
    def __init__(self, clauses, restart, deletion, decision):
        self.unit_prop_counter = 0
        self.decisions_counter = 0
        self.checked_clauses_counter = 0

        self.deletion = deletion
        self.restarts_counter = 0
        self.original_clauses_number = len(clauses)

        self.restart_type = restart
        self.decision = decision
        if restart is None:
            self.conflicts_maximum = float('inf')
        else:
            self.conflicts_maximum = 4
            if restart == "Luby":
                self.luby = Luby()

        self.reinitialize(clauses)

    def reinitialize(self, clauses):
        self.clauses = clauses      # list containing all clauses
        self.assignment = []        # queue containing assigned literals
        self.dec_levels = []        # similar queue but containing decision levels of corresponding assigned literals
        self.antecedents = dict()   # mapping from literals to clause indices
        self.decision_level = 0     # current decision level
        self.conflicts_counter = 0

        self.watched_literals = dict()
        self.unit_literals = set()  # set of literals used during unit propagation

        self.literal_occurences_number = dict()

        for i, clause in enumerate(clauses):
            for literal in clause:
                # watched literals initialization
                if literal not in self.watched_literals:
                    self.watched_literals[literal] = set()
                if -literal not in self.watched_literals:
                    self.watched_literals[-literal] = set()

                # literals occurrences counting
                if literal not in self.literal_occurences_number:
                    self.literal_occurences_number[literal] = 1
                else:
                    self.literal_occurences_number[literal] += 1
                if -literal not in self.literal_occurences_number:
                    self.literal_occurences_number[-literal] = 0

        # watched literals setting & unit clauses finding
        for i, clause in enumerate(clauses):
            self.watched_literals[clause[0]].add(i)
            if len(clause) >= 2:
                self.watched_literals[clause[1]].add(i)
            elif len(clause) == 1:
                self.unit_literals.add(clause[0])
        self.unassigned_literals = list(self.watched_literals.keys())

    def decide_literal(self):
        if len(self.unassigned_literals) == 0:
            return None

        self.decisions_counter += 1
        if self.decision == 'random':
            return random.choice(self.unassigned_literals)

        elif self.decision == 'most_common':
            most_common_literal = 0
            max_occurrences = 0
            for l in self.unassigned_literals:
                if self.literal_occurences_number[l] >= max_occurrences:
                    most_common_literal = l
                    max_occurrences = self.literal_occurences_number[l]
            return most_common_literal

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
        self.unassigned_literals.remove(literal)
        self.unassigned_literals.remove(-literal)

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
        """Returns backtrack level, learned clause and the latest assigned literal from this clause"""
        self.conflicts_counter += 1

        if self.conflicts_counter > self.conflicts_maximum:
            return -10, None, None

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
        for l in clause:
            self.literal_occurences_number[l] += 1

        self.antecedents[unit_literal] = new_clause_index
        self.unit_literals = {unit_literal}

    def backtrack(self, backtrack_level):
        while len(self.assignment) > 0 and self.dec_levels[-1] > backtrack_level:
            l = self.assignment.pop()
            self.dec_levels.pop()
            self.unassigned_literals.append(l)
            self.unassigned_literals.append(-l)
        self.decision_level = backtrack_level

    def restart(self):
        self.restarts_counter += 1

        if self.restart_type == "geometric":
            self.conflicts_maximum *= 1.5
        elif self.restart_type == "Luby":
            self.conflicts_maximum = self.luby.constant * self.luby.get_next()

        new_clauses = self.delete_clauses()
        self.reinitialize(new_clauses)

    def delete_clauses(self):
        if self.deletion is None:
            return self.clauses

        new_clauses = self.clauses[:self.original_clauses_number]
        if self.deletion == "short":
            for i in range(self.original_clauses_number, len(self.clauses)):
                if len(self.clauses[i]) <= math.log2(self.restarts_counter) + 1:
                    new_clauses.append(self.clauses[i])

        elif self.deletion == "LBD":
            decision_levels_counter = set()
            for i in range(self.original_clauses_number, len(self.clauses)):
                decision_levels_counter.clear()
                for l in self.clauses[i]:
                    if -l in self.assignment:
                        dec_level = self.dec_levels[self.assignment.index(-l)]
                        decision_levels_counter.add(dec_level)
                if len(decision_levels_counter) <= math.log2(self.restarts_counter) + 1:
                    new_clauses.append(self.clauses[i])

        elif self.deletion == "active":
            clause_activity = dict()

            for clause_index in self.antecedents.values():
                if clause_index >= self.original_clauses_number:
                    if clause_index in clause_activity:
                        clause_activity[clause_index] += 1
                    else:
                        clause_activity[clause_index] = 1
            for i in range(self.original_clauses_number, len(self.clauses)):
                if i in clause_activity and clause_activity[i] >= math.log10(self.restarts_counter) - 1:
                        new_clauses.append(self.clauses[i])

        self.original_clauses_number = len(new_clauses)
        return new_clauses

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
            else:
                self.restart()

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

    solver = CDCL_solver(clauses, args.restart, args.deletion, args.decision)

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