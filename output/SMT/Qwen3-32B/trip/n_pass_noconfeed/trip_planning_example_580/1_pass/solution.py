import z3
import json

solver = z3.Solver()

# Define cities as 0-4: 0=Geneva, 1=Paris, 2=Porto, 3=Oslo, 4=Reykjavik
order = [z3.Int(f'order_{i}') for i in range(5)]

# Constraints for order
# All distinct
solver.add(z3.Distinct(order))
# First city is Geneva (0)
solver.add(order[0] == 0)

# Allowed transitions (bidirectional)
allowed_edges = [
    # Paris-Oslo
    (1, 3), (3, 1),
    # Geneva-Oslo
    (0, 3), (3, 0),
    # Porto-Paris
    (2, 1), (1, 2),
    # Geneva-Paris
    (0, 1), (1, 0),
    # Geneva-Porto
    (0, 2), (2, 0),
    # Paris-Reykjavik
    (1, 4), (4, 1),
    # Reykjavik-Oslo
    (4, 3), (3, 4),
    # Porto-Oslo
    (2, 3), (3, 2),
]

# For each consecutive pair in the order, check allowed transitions
for i in range(4):
    current = order[i]
    next_city = order[i + 1]
    # Create a constraint that (current, next_city) is in allowed_edges
    allowed = []
    for a, b in allowed_edges:
        allowed.append(z3.And(current == a, next_city == b))
    solver.add(z3.Or(allowed))

# Define durations for each city
durations = {0: 7, 1: 6, 2: 7, 3: 5, 4: 2}

# Define start and end days for each segment in the order
start = [z3.Int(f'start_{i}') for i in range(5)]
end = [z3.Int(f'end_{i}') for i in range(5)]

# First start is 1
solver.add(start[0] == 1)

# For each segment, end = start + duration - 1
for i in range(5):
    # duration_i depends on order[i]
    duration_i = z3.If(order[i] == 0, 7,
                         z3.If(order[i] == 1, 6,
                               z3.If(order[i] == 2, 7,
                                     z3.If(order[i] == 3, 5,
                                           z3.If(order[i] == 4, 2, 0)))))
    solver.add(end[i] == start[i] + duration_i - 1)

# For consecutive segments, start[i+1] = end[i]
for i in range(4):
    solver.add(start[i + 1] == end[i])

# The last end day must be 23
solver.add(end[4] == 23)

# Oslo (3) must have its segment overlapping day 19-23
for i in range(5):
    solver.add(z3.Implies(order[i] == 3, z3.And(start[i] <= 23, end[i] >= 19)))

# Check if the solver can find a solution
if solver.check() == z3.sat:
    model = solver.model()
    # Extract order, start, end
    order_values = [model.eval(order[i]).as_long() for i in range(5)]
    start_values = [model.eval(start[i]).as_long() for i in range(5)]
    end_values = [model.eval(end[i]).as_long() for i in range(5)]

    # Now map the order to city names
    city_names = {0: 'Geneva', 1: 'Paris', 2: 'Porto', 3: 'Oslo', 4: 'Reykjavik'}

    # Build the itinerary
    itinerary = []
    for i in range(5):
        city_idx = order_values[i]
        city = city_names[city_idx]
        s = start_values[i]
        e = end_values[i]
        day_range = f"Day {s}-{e}"
        itinerary.append({"day_range": day_range, "place": city})

    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")