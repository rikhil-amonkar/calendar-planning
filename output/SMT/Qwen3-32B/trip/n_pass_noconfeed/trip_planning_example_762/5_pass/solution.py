import z3

# Assuming cities_order is a list of z3 integer variables
# Example: cities_order = [z3.Int(f'city_{i}') for i in range(n_cities)]

solver = z3.Solver()
solver.add(z3.Distinct(cities_order))

# Optionally, check for satisfiability
result = solver.check()
if result == z3.sat:
    print("Solution found:", solver.model())
else:
    print("No solution found.")