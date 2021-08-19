import sys
import argparse
import time
from formula2cnf import load_smtlib


parser = argparse.ArgumentParser()
parser.add_argument('infile', nargs='?', type=argparse.FileType('r', encoding='UTF-8'), default=sys.stdin)
parser.add_argument('--decision_heuristics', type=bool, default=False)


def decide_literal_heuristics(clauses, satisfied_clauses):
    global decisions_counter
    decisions_counter += 1

    min_clause_length = len(clauses[0])
    for i, clause in enumerate(clauses):
        if not satisfied_clauses[i]:
            if len(clause) == 2:
                #  immediately returning a literal located in a clause of length 2
                return clause[0]
            if len(clause) <= min_clause_length:
                #  finding a literal located in the shortest clause
                literal = clause[0]
                min_clause_length = len(clause)
    return literal


def decide_literal(assignment, adjacency_list):
    for literal in adjacency_list.keys():
        if literal not in assignment and -literal not in assignment:
            global decisions_counter
            decisions_counter += 1
            return literal
    return None


def load_dimacs(input):
    line = input.readline()
    while line[0] == 'c':
        line = input.readline()
    _, _, nbvar, nbclauses = line.split()

    clauses = []
    for i in range(int(nbclauses)):
        clause = [int(var) for var in input.readline().split() if var != '0']
        clauses.append(clause)
    return clauses


def get_adjacency_list(clauses):
    ad_list = dict()
    # initialization of lists
    for clause in clauses:
        for literal in clause:
            if literal not in ad_list:
                ad_list[literal] = []
            if -literal not in ad_list:
                ad_list[-literal] = []

    for i, clause in enumerate(clauses):
        for literal in clause:
            ad_list[literal].append(i)

    return ad_list


def unit_prop(literal, clauses, adjacency_list, satisfied_clauses, assignment):
    """Apply unit propagation recursively until some unit clause exists"""

    global checked_clauses_counter
    global unit_prop_counter

    # finding unit clause if literal for unit propagation not given
    if literal is None:
        for i, clause in enumerate(clauses):
            if len(clause) == 0:
                return True, None, None, None
            if len(clause) == 1 and not satisfied_clauses[i]:
                literal = clause[0]
        if literal is None:
            return False, clauses, satisfied_clauses, assignment
    unit_prop_counter += 1

    # satisfying clauses containing the literal
    assignment.append(literal)
    for clause_index in adjacency_list[literal]:
        checked_clauses_counter += 1

        if not satisfied_clauses[clause_index]:
            satisfied_clauses[clause_index] = True

    # removing literal negations from appropriate clauses
    next_literal = None
    unsat = False
    for clause_index in adjacency_list[-literal]:
        checked_clauses_counter += 1

        clauses[clause_index].remove(-literal)
        if len(clauses[clause_index]) == 0:
            unsat = True
        if len(clauses[clause_index]) == 1:
            lit = clauses[clause_index][0]
            if lit not in assignment:
                next_literal = lit
    if unsat:
        return True, None, None, None

    return unit_prop(next_literal, clauses, adjacency_list, satisfied_clauses, assignment)


def dpll(clauses, adjacency_list, satisfied_clauses, assignment, literal_to_satisfy=None, heuristics=False):

    unsat, clauses, satisfied_clauses, assignment = unit_prop(literal_to_satisfy, clauses, adjacency_list, satisfied_clauses, assignment)

    if unsat:
        return None
    if all(satisfied_clauses):
        return assignment

    if heuristics:
        current_literal = decide_literal_heuristics(clauses, satisfied_clauses)
    else:
        current_literal = decide_literal(assignment, adjacency_list)
    original_sat_clauses = satisfied_clauses[:]

    result = dpll(clauses, adjacency_list, satisfied_clauses, assignment, current_literal, heuristics)
    if result is None:
        #  backtracking
        index_of_current_literal = assignment.index(current_literal)
        literals_to_backtrack = assignment[index_of_current_literal:]
        for l in literals_to_backtrack:
            assignment.pop()
            for clause_index in adjacency_list[-l]:
                clauses[clause_index].append(-l)
    else:
        return result

    result = dpll(clauses, adjacency_list, original_sat_clauses, assignment, -current_literal, heuristics)

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

    adjacency_list = get_adjacency_list(clauses)

    unit_prop_counter = 0
    decisions_counter = 0
    checked_clauses_counter = 0

    start = time.time()
    assignment = dpll(clauses, adjacency_list, [False for i in clauses], [], heuristics=args.decision_heuristics)
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




