import matplotlib.pyplot as plt

'''ploot(number_of_variables[:5], dpll_CPU_time, 'dpll')
ploot(number_of_variables, dpll_h_CPU_time, 'dpll with heuristics')

plt.yscale('log')
plt.xlabel('number of variables')
plt.ylabel('CPU time [s]')'''

'''ploot(number_of_variables[:5], dpll_CPU_time, 'dpll - adjacency lists')
ploot(number_of_variables[:5], dpll_w_CPU_time, 'dpll - watched literals')

plt.yscale('log')
plt.xlabel('number of variables')
plt.ylabel('CPU time [s]')'''


number_of_variables = [50, 75, 100, 125, 150, 175, 200]

dpll_h_CPU_time = [0.01, 0.13, 1.86, 5.89, 62.81, 387.86, 2289.29]

dpll_w_CPU_time = [0.07, 0.74, 13.64, 5.51, 2068.71]
dpll_w_checked_clauses = [24717, 203287, 3224053, 1288421, 357288056]

dpll_CPU_time = [0.09, 0.85, 25.36, 14.49, 3396.05]
dpll_checked_clauses = [79206, 681634, 12040982, 4981417, 1438357866]


def ploot(x, y, label):
    plt.plot(x, y, linestyle='--', marker='o', markersize=5, label=label)

plt.figure()

ploot(number_of_variables[:5], dpll_checked_clauses, 'dpll - adjacency lists')
ploot(number_of_variables[:5], dpll_w_checked_clauses, 'dpll - watched literals')

plt.yscale('log')
plt.xlabel('number of variables')
plt.ylabel('number of checked clauses')
plt.legend()
plt.show()
