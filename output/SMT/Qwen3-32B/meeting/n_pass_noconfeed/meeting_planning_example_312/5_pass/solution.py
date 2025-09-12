import z3

# Define an integer variable
travel_time = z3.Int('travel_time')

# Create a solver instance
solver = z3.Solver()

# Add a constraint
solver.add(travel_time == 10)

# Check for satisfiability and print the model if satisfied
if solver.check() == z3.sat:
    print(solver.model())