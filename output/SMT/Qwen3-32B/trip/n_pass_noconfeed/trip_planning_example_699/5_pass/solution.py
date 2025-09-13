solver = z3.Solver()
solver.add(constraint)
result = solver.check()
if result == z3.sat:
    model = solver.model()
    print(model)