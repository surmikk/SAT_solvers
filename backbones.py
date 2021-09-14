from formula2cnf import load_smtlib
from dpll import load_dimacs
from cdcl import CDCL_solver
import argparse
import sys

parser = argparse.ArgumentParser()
parser.add_argument('infile', nargs='?', type=argparse.FileType('r', encoding='UTF-8'), default=sys.stdin)


if __name__ == "__main__":
    args = parser.parse_args()

    file_suffix = args.infile.name.split('.')[-1]

    if file_suffix == 'sat':
        clauses, variables_mapping = load_smtlib(args.infile)
    elif file_suffix == 'cnf':
        clauses = load_dimacs(args.infile)
    else:
        raise Exception("Unknown file type")

    # first solve formula itself
    solver = CDCL_solver(clauses, 'Luby', 'active', 'Jeroslow-Wang', assumptions=[])
    assignment = solver.solve()

    if assignment is None:
        # if the formula is UNSAT, then no backbones exist
        possible_backbones = set()
    else:
        # otherwise possible backbones are just the literals from the found assignment
        possible_backbones = set(assignment)

    backbones = set()
    original_clauses = solver.clauses  # we can use original clauses together with learned ones from the first run
    solver_runs = 1

    while len(possible_backbones) > 0:
        solver_runs += 1
        literal = possible_backbones.pop()

        clauses = original_clauses[:]
        clauses.append([-literal])

        solver = CDCL_solver(clauses, 'Luby', 'active', 'Jeroslow-Wang', assumptions=[])
        assignment = solver.solve()

        if assignment is not None:
            # '+literal' cannot be a backbone
            # we can reduce 'possible_backbones' because they must be contained again in found assignment
            possible_backbones = possible_backbones.intersection(set(assignment)).difference(backbones)

        else:
            # there exists no model where '-literal' holds, so 'literal' is a backbone
            backbones.add(literal)

    if len(backbones) == 0:
        print('No backbones exist')
    else:
        print(str(len(backbones)), 'backbones:')
        print(backbones)
    print('Number of solver runs:', solver_runs)
