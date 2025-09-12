# Alternative clearer implementation for clue 4:
for i in range(3):
    solver.add(Implies(drink_vars[i] == water_index, vacation_vars[i] == mountain_index))
    solver.add(Implies(vacation_vars[i] == mountain_index, drink_vars[i] == water_index))