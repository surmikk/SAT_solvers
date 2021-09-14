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
    # we can work with solver's clauses (where are updated learned clauses), since we use assumptions
    all_clauses = solver.clauses

    while len(possible_backbones) > 0:
        literal = possible_backbones.pop()

        assumptions = [-literal]
        solver = CDCL_solver(all_clauses, 'Luby', 'active', 'Jeroslow-Wang', assumptions=assumptions)
        assignment = solver.solve()

        if -literal in assignment:
            # 'literal' cannot be a backbone
            continue
        else:
            # we assumed '-literal', but it's not in the assignment, it had to be deleted from assignment because
            # of some confilct. This conflict must have been caused by this '-literal', so any assignment
            # cannot contain '-literal' which means that 'literal' is a backbone.
            backbones.add(literal)
            possible_backbones = possible_backbones.intersection(set(assignment)).difference(backbones)

    if len(backbones) == 0:
        print('No backbones exist')
    else:
        print(str(len(backbones)), 'backbones:')
        print(backbones)
