from ortools.sat.python import cp_model

model = cp_model.CpModel()
# Define variables and constraints here...

# Solve the model
solver = cp_model.CpSolver()
status = solver.Solve(model)

if status == cp_model.OPTIMAL:
    # Now extract values using solver.Value(...)