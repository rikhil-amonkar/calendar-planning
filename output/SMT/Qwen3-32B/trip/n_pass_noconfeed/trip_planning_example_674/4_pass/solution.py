import z3

# Create a Z3 solver instance
solver = z3.Solver()

# Define arrays of Z3 integer variables
S = [z3.Int(f'S_{i}') for i in range(6)]
order = [z3.Int(f'order_{i}') for i in range(6)]

# Define the last_day expression based on S[5] and order[5]
last_day = S[5] + z3.If(order[5] == 0, 2,
                        z3.If(order[5] == 1, 3,
                              z3.If(order[5] == 2, 4,
                                    z3.If(order[5] == 3, 4,
                                          z3.If(order[5] == 4, 2,
                                                z3.If(order[5] == 5, 4, 0)))))) - 1

# Example: Add constraints or assert the expression
# For demonstration, we can add a simple constraint
solver.add(last_day > 0)

# Check if the constraints are satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    print("Model found:")
    for i in range(6):
        print(f"S_{i} = {model[S[i]]}")
        print(f"order_{i} = {model[order[i]]}")
    print(f"last_day = {model.evaluate(last_day)}")
else:
    print("No solution found.")