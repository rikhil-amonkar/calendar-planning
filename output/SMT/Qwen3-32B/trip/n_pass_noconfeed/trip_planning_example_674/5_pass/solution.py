import z3

# Create a Z3 solver instance
solver = z3.Solver()

# Define arrays of Z3 integer variables
S = [z3.Int(f'S_{i}') for i in range(6)]
order = [z3.Int(f'order_{i}') for i in range(6)]

# Add constraints for order variables
solver.add([z3.And(0 <= order[i], order[i] <= 5) for i in range(6)])
solver.add(z3.Distinct(order))

# Add constraints for start time variables
solver.add([S[i] >= 0 for i in range(6)])

# Define last_day based on S[5] and order[5]
last_day = S[5] + z3.If(order[5] == 0, 2,
                        z3.If(order[5] == 1, 3,
                              z3.If(order[5] == 2, 4,
                                    z3.If(order[5] == 3, 4,
                                          z3.If(order[5] == 4, 2,
                                                z3.If(order[5] == 5, 4, 0)))))) - 1

# Check if the constraints are satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    print("Valid plan found:")
    for i in range(6):
        print(f"S_{i} = {model[S[i]]}")
        print(f"order_{i} = {model[order[i]]}")
    print(f"last_day = {model.evaluate(last_day)}")
else:
    print("No valid plan found.")