import z3

# Define an integer variable
day = z3.Int('day')

# Initialize the Z3 solver
opt = z3.Solver()

# Add the constraint: 1 <= day <= 4
opt.add(z3.And(1 <= day, day <= 4))

# Check if the constraints are satisfiable
if opt.check() == z3.sat:
    model = opt.model()
    print(f"Solution: day = {model[day]}")
else:
    print("No solution found.")