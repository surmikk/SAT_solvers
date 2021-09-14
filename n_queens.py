from pysat.solvers import Glucose4, Cadical, Minisat22, Lingeling, Solver
from pysat.formula import CNF
from pysat.card import CardEnc, EncType
import os
import time

def create_formula(n):
    # supposing that chessboard is numbered row by row
    formula = CNF()

    # horizontal constraints
    for i in range(1, n*n + 1, n):
        formula.extend(CardEnc.equals(range(i, i + n), encoding=EncType.pairwise))

    # vertical constraints
    for i in range(1, n + 1):
        formula.extend(CardEnc.equals(range(i, i + n*n, n), encoding=EncType.pairwise))

    # oblique constraints
    for i in range(1, n):
        formula.extend(CardEnc.atmost(range(i, (n-i+1)* (n+1), n+1), encoding=EncType.pairwise))
    for i in range(2, n+1):
        formula.extend(CardEnc.atmost(range(i, i*n, n-1), encoding=EncType.pairwise))
    for index, i in enumerate(range(n+1, n*n -n +1, n)):
        formula.extend(CardEnc.atmost(range(i, i + (n -index -1) * (n+1), n+1), encoding=EncType.pairwise))
    for index, i in enumerate(range(2*n, n*n, n)):
        formula.extend(CardEnc.atmost(range(i, i + (n -index -1) * (n-1), n-1), encoding=EncType.pairwise))

    return formula

def run_solver(solver):
    start = time.time()
    result = solver.solve()
    end = time.time()
    return "{:.3f}".format(end - start)

chessboard_sizes = range(200, 440, 40)
for i in chessboard_sizes:
    path = 'queens_' + str(i) + '.cnf'
    if os.path.isfile(path):
        continue
    formula = create_formula(i)
    formula.to_file(path)

for solver_name in ['glucose4', 'cadical', 'minisat22', 'lingeling']:
    print(solver_name)
    for size in chessboard_sizes:
        solver = Solver(name=solver_name)
        cnf = CNF()
        cnf.from_file(fname='queens_' + str(size) + '.cnf')
        solver.append_formula(cnf.clauses)
        print(size, run_solver(solver))
    print()
