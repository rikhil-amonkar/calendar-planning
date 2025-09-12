from ortools.sat.python import cp_model

model = cp_model.CpModel()
# ... (define variables and constraints)

solver = cp_model.CpSolver()
status = solver.Solve(model)

if status == cp_model.OPTIMAL or status == cp_model.FEASIBLE:
    # Now extract the solution
    order = [0] + [solver.Value(order_vars[i]).as_long() for i in range(1, 7)]
    starts = [solver.Value(start_days[i]).as_long() for i in range(7)]
    # ... (rest of your logic)
else:
    print("No solution found.")