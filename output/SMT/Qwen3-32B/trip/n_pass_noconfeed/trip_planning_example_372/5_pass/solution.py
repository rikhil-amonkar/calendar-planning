from z3 import Solver, Int, Array, Store, Select, IntSort, And

# Initialize solver
solver = Solver()

# Required durations for each city
required_duration = {0: 2, 1: 7, 2: 3, 3: 4}

# Define variables
s = [Int(f's_{i}') for i in range(4)]
seq = [Int(f'city_{i}') for i in range(4)]

# Ensure each city is in the range [0, 3]
for city_var in seq:
    solver.add(And(city_var >= 0, city_var <= 3))

# Create a Z3 array to map city index to required duration
duration_array = Array('duration_array', IntSort(), IntSort())
for i in range(4):
    duration_array = Store(duration_array, i, Int(required_duration[i]))

# Add constraints for each city
for i in range(4):
    city = seq[i]
    si = s[i]
    in_transitions = 1 if i > 0 else 0
    out_transitions = 1 if i < 3 else 0

    # Get the required duration using Z3 array
    rd = Select(duration_array, city)

    # Add the constraint
    solver.add(si + in_transitions + out_transitions == rd)

# Example: Check if the problem is satisfiable
print(solver.check())
if solver.check() == 'sat':
    print(solver.model())