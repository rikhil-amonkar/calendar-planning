# Add bounds and distinct constraints for each attribute
for var in [n, s, c, h, p]:
    for i in range(houses):
        solver.add(And(var[i] >= 0, var[i] <= 3))
    solver.add(Distinct(var[0], var[1], var[2], var[3]))