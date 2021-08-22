import sys
import argparse
import time

from formula2cnf import load_smtlib
from dpll import load_dimacs

parser = argparse.ArgumentParser()
parser.add_argument('infile', nargs='?', type=argparse.FileType('r', encoding='UTF-8'), default=sys.stdin)


def decide_literal(assignment, watched_literals):
    for literal in watched_literals.keys():
        if literal not in assignment and -literal not in assignment:
            global decisions_counter
            decisions_counter += 1
            return literal
    return None


def get_watched_literals(clauses):
    w_lits = dict()
    unit_literals = set()

    for i, clause in enumerate(clauses):
        for literal in clause:
            if literal not in w_lits:
                w_lits[literal] = set()
            if -literal not in w_lits:
                w_lits[-literal] = set()

    for i, clause in enumerate(clauses):
        w_lits[clause[0]].add(i)
        if len(clause) >= 2:
            w_lits[clause[1]].add(i)
        elif len(clause) == 1:
            unit_literals.add(clause[0])

    return w_lits, unit_literals


def unit_prop(literal, clauses, watched_literals, assignment):
    """Unit propagate given literal"""

    global unit_prop_counter
    global checked_clauses_counter
    unit_prop_counter += 1
    assignment.append(literal)

    # trying to change watched literals in clauses where 'not literal' is watched
    found_unit_literals = set()
    not_longer_watched = list()

    unsat = False
    for clause_index in watched_literals[-literal]:
        checked_clauses_counter += 1
        next_watched_literal = None
        possible_unit_literal = None
        possible_unit_literal_satisfied = None

        if len(clauses[clause_index]) == 1:
            unsat = True
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
            elif not possible_unit_literal_satisfied:
                unsat = True
        else:
            not_longer_watched.append(clause_index)
            watched_literals[next_watched_literal].add(clause_index)


    for clause_index in not_longer_watched:
        watched_literals[-literal].remove(clause_index)

    if unsat:
        return None
    else:
        return found_unit_literals


def dpll_watched(clauses, watched_literals, assignment, literals_to_satisfy):
    # unit propagation
    while len(literals_to_satisfy) > 0:
        result = unit_prop(literals_to_satisfy.pop(), clauses, watched_literals, assignment)
        if result is None:
            return None
        else:
            literals_to_satisfy = literals_to_satisfy.union(result)


    current_literal = decide_literal(assignment, watched_literals)
    if current_literal == None:
        # all literals assigned
        return assignment


    result = dpll_watched(clauses, watched_literals, assignment, {current_literal})
    if result is None:
        #  backtracking
        index_of_current_literal = assignment.index(current_literal)
        literals_to_backtrack = assignment[index_of_current_literal:]
        for _ in literals_to_backtrack:
            assignment.pop()
    else:
        return result


    result = dpll_watched(clauses, watched_literals, assignment, {-current_literal})
    if result is None:
        return None
    else:
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

    watched_literals, literals_to_satisfy = get_watched_literals(clauses)

    unit_prop_counter = 0
    decisions_counter = 0
    checked_clauses_counter = 0

    start = time.time()
    assignment = dpll_watched(clauses, watched_literals, [], literals_to_satisfy)
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