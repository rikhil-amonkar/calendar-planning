import z3
import json

# Initialize Z3 solver
solver = z3.Solver()

# Define cities and their durations
cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
durations = [7, 5, 4, 2]  # durations for each city in the same order

# Variables for the order of cities (positions 0-3)
o0, o1, o2, o3 = [z3.Int(f'order_{i}') for i in range(4)]
order = [o0, o1, o2, o3]

# Constraints: all distinct and in 0-3
solver.add(z3.Distinct(order))
for var in order:
    solver.add(var >= 0, var <= 3)

# Allowed transitions between cities
allowed_transitions = [
    (0, 3), (3, 0),  # Manchester-Vienna
    (0, 1), (1, 0),  # Manchester-Stuttgart
    (0, 2), (2, 0),  # Manchester-Madrid
    (3, 1), (1, 3),  # Vienna-Stuttgart
    (3, 2), (2, 3),  # Vienna-Madrid
]

# Add constraints for transitions between consecutive cities
for i in range(3):
    prev = order[i]
    next_city = order[i + 1]
    constraints = []
    for a, b in allowed_transitions:
        constraints.append(z3.And(prev == a, next_city == b))
    solver.add(z3.Or(*constraints))

# Variables for start and end days
start_day = [z3.Int(f'start_day_{i}') for i in range(4)]
end_day = [z3.Int(f'end_day_{i}') for i in range(4)]

# First day starts at 1
solver.add(start_day[0] == 1)

# Link start and end days
for i in range(3):
    solver.add(start_day[i + 1] == end_day[i])

# Compute end_day[i] = start_day[i] + duration_i - 1
for i in range(4):
    duration_i = z3.If(order[i] == 0, 7,
                       z3.If(order[i] == 1, 5,
                             z3.If(order[i] == 2, 4, 2)))
    solver.add(end_day[i] == start_day[i] + duration_i - 1)

# Constraints for workshop and wedding
for i in range(4):
    # Wedding in Manchester between day 1-7
    solver.add(z3.Implies(order[i] == 0, z3.And(start_day[i] <= 7, end_day[i] >= 1)))
    # Workshop in Stuttgart between day 11-15
    solver.add(z3.Implies(order[i] == 1, z3.And(start_day[i] <= 15, end_day[i] >= 11)))

# Check if the constraints are satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    # Extract the order
    order_values = [model.eval(var).as_long() for var in order]
    # Extract start and end days
    start_days = [model.eval(sd).as_long() for sd in start_day]
    end_days = [model.eval(ed).as_long() for ed in end_day]
    
    # Build the itinerary
    itinerary = []
    for i in range(4):
        city_index = order_values[i]
        city_name = cities[city_index]
        start = start_days[i]
        end = end_days[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city_name})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")