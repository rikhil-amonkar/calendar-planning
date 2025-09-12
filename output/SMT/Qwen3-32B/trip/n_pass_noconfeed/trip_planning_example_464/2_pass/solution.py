# Constraints: order is a permutation of 0-4
solver.add([0 <= order[i] <= 4 for i in range(5)])
solver.add(Distinct(order))