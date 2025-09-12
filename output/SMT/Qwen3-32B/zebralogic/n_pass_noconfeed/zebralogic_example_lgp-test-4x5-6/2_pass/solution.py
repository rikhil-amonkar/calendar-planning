# Clue 11: Red (1) directly left of white (3)
for i in range(n - 1):
    solver.add(Implies(color[i] == 1, color[i+1] == 3))