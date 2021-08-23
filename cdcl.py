import sys
import argparse
import time
from abc import ABC, abstractmethod

from formula2cnf import load_smtlib
from dpll import load_dimacs
from dpll_watched import get_watched_literals

parser = argparse.ArgumentParser()
parser.add_argument('infile', nargs='?', type=argparse.FileType('r', encoding='UTF-8'), default=sys.stdin)


def decide_literal(assignment, watched_literals):
    for literal in watched_literals.keys():
        if literal not in assignment and -literal not in assignment:
            global decisions_counter
            decisions_counter += 1
            return literal
    return None

def unit_propagation(literals_to_satisfy, clauses, watched_literals, assignment, dec_levels, antecedents, dec_level):
    conflict_clause = -1
    while len(literals_to_satisfy) > 0:
        unit_literal = literals_to_satisfy.pop()
        assignment.append(unit_literal)
        dec_levels.append(dec_level)
        conflict_clause, unit_literals = unit_prop_literal(unit_literal, clauses, watched_literals, assignment, antecedents)
        if conflict_clause >= 0:
            return conflict_clause
        else:
            literals_to_satisfy = literals_to_satisfy.union(unit_literals)

    return conflict_clause


def unit_prop_literal(literal, clauses, watched_literals, assignment, antecedents):
    global unit_prop_counter
    global checked_clauses_counter
    unit_prop_counter += 1

    # trying to change watched literals in clauses where 'not literal' is watched
    found_unit_literals = set()
    not_longer_watched = list()
    conflict_clause = -1

    for clause_index in watched_literals[-literal]:
        checked_clauses_counter += 1
        next_watched_literal = None
        possible_unit_literal = None
        possible_unit_literal_satisfied = None

        if len(clauses[clause_index]) == 1:
            conflict_clause = clause_index
            continue

        neg_literal_offset = clauses[clause_index].index(-literal)
        for i in range(neg_literal_offset + 1, neg_literal_offset + len(clauses[clause_index])):
            l = clauses[clause_index][i % len(clauses[clause_index])]
            if clause_index in watched_literals[l]:
                # 'l' is another watched literal in this clause
                possible_unit_literal = l
                if possible_unit_literal in assignment:
                    possible_unit_literal_satisfied = True
                if -possible_unit_literal in assignment:
                    possible_unit_literal_satisfied = False
            else:
                if not next_watched_literal and -l not in assignment:
                    next_watched_literal = l

        if next_watched_literal is None:
            # watched 'literal' cannot move in this clause
            if possible_unit_literal_satisfied is None:
                found_unit_literals.add(possible_unit_literal)
                antecedents[possible_unit_literal] = clause_index
            elif not possible_unit_literal_satisfied:
                conflict_clause = clause_index
        else:
            not_longer_watched.append(clause_index)
            watched_literals[next_watched_literal].add(clause_index)

    for clause_index in not_longer_watched:
        watched_literals[-literal].remove(clause_index)

    return conflict_clause, found_unit_literals


def conflict_analysis(conflict_clause, clauses, antecedents, decision_levels, current_decision_level, assignment):
    # finding an assertive clause with 1-UIP

    C = set(clauses[conflict_clause])

    while True:
        literals_at_d_counter = 0
        latest_assignment_time = -1
        second_latest_ass_time = -1
        for literal in C:
            assignment_time = assignment.index(-literal)
            if decision_levels[assignment_time] == current_decision_level:
                literals_at_d_counter += 1
            if assignment_time >= latest_assignment_time:
                second_latest_ass_time = latest_assignment_time
                latest_assignment_time = assignment_time
            elif assignment_time > second_latest_ass_time:
                second_latest_ass_time = assignment_time

        if literals_at_d_counter <= 1:
            learned_clause = list(C)
            if len(learned_clause) == 1:
                if current_decision_level == 0:
                    return -1, None, None
                else:
                    return 0, learned_clause, learned_clause[0]
            else:
                return decision_levels[second_latest_ass_time], learned_clause, -assignment[latest_assignment_time]


        l = -assignment[latest_assignment_time]
        C.remove(l)
        for literal in clauses[antecedents[-l]]:
            if literal != -l:
                C.add(literal)


def join_learned_clause(clause, literal, clauses, watched_literals, antecedents):
    new_clause_index = len(clauses)
    clauses.append(clause)
    watched_literals[literal].add(new_clause_index)
    if len(clause) >= 2:
        if literal != clause[0]:
            watched_literals[clause[0]].add(new_clause_index)
        else:
            watched_literals[clause[1]].add(new_clause_index)

    antecedents[literal] = new_clause_index


def backtrack(backtrack_level, assignment, dec_levels):
    while len(assignment) > 0 and dec_levels[-1] > backtrack_level:
        assignment.pop()
        dec_levels.pop()


def cdcl(clauses, watched_literals, literals_to_satisfy):
    assignment = []
    dec_levels = []
    antecedents = dict()
    decision_level = 0

    conflict_clause = unit_propagation(literals_to_satisfy, clauses, watched_literals, assignment, dec_levels, antecedents, decision_level)
    if conflict_clause >= 0:
        return None

    while True:
        current_literal = decide_literal(assignment, watched_literals)
        decision_level += 1

        if current_literal == None:
            # all variables assigned
            return assignment
        literals_to_satisfy = {current_literal}

        while True:
            conflict_clause = unit_propagation(literals_to_satisfy, clauses, watched_literals, assignment, dec_levels, antecedents, decision_level)
            if conflict_clause == -1:
                break

            backtrack_level, learned_clause, new_unit_literal = conflict_analysis(conflict_clause, clauses, antecedents, dec_levels, decision_level, assignment)
            if backtrack_level == -1:
                return None

            join_learned_clause(learned_clause, new_unit_literal, clauses, watched_literals, antecedents)
            literals_to_satisfy = {new_unit_literal}
            backtrack(backtrack_level, assignment, dec_levels)
            decision_level = backtrack_level











if __name__ == "__main__":
    args = parser.parse_args()

    file_suffix = args.infile.name.split('.')[-1]

    if file_suffix == 'sat':
        clauses, variables_mapping = load_smtlib(args.infile)
    elif file_suffix == 'cnf':
        clauses = load_dimacs(args.infile)
    else:
        raise Exception("Unknown file type")

    watched_literals, literals_to_satisfy = get_watched_literals(clauses)

    unit_prop_counter = 0
    decisions_counter = 0
    checked_clauses_counter = 0

    start = time.time()
    assignment = cdcl(clauses, watched_literals, literals_to_satisfy)
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
    print('CPU time:', end - start)
    print('number of decisions:', decisions_counter)
    print('number of steps of unit propagation:', unit_prop_counter)
    print('total number of checked clauses:', checked_clauses_counter)