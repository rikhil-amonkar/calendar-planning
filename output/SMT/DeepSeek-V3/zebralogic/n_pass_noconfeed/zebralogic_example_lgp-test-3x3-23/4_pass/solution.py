from ortools.sat.python import cp_model

# Create the model
model = cp_model.CpModel()

# Your constraint should be added to the model, not the solver
model.add(
    (hobby_vars[h-1] == hobbies.index('photography')) == 
    (occupation_vars[h-1] == occupations.index('teacher'))
)

# Then later create the solver and solve
solver = cp_model.CpSolver()
status = solver.solve(model)