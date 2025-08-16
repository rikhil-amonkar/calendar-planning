import z3

# Initialize the solver
solver = z3.Solver()

# Define the order variables for the 5 cities
order = [z3.Int(f'order_{i}') for i in range(5)]
# Define start and end variables for each segment
start = [z3.Int(f'start_{i}') for i in range(5)]
end = [z3.Int(f'end_{i}') for i in range(5)]

# Constraints: order variables must be between 0 and 4 and distinct
for i in range(5):
    solver.add(z3.And(0 <= order[i], order[i] <= 4))
solver.add(z3.Distinct(order))

# First start is day 1
solver.add(start[0] == 1)

# Subsequent starts are the end of the previous segment
for i in range(1, 5):
    solver.add(start[i] == end[i-1])

# Define durations based on the city
for i in range(5):
    duration = z3.If(order[i] == 0, 7,
                     z3.If(order[i] == 1, 6,
                           z3.If(order[i] == 2, 5,
                                 z3.If(order[i] == 3, 7, 2))))
    solver.add(end[i] == start[i] + duration - 1)

# Last end must be day 23
solver.add(end[4] == 23)

# Allowed direct flights between cities
allowed_flights = [
    (0, 1), (1, 0),
    (0, 3), (3, 0),
    (0, 2), (2, 0),
    (1, 2), (2, 1),
    (1, 3), (3, 1),
    (1, 4), (4, 1),
    (4, 2), (2, 4),
    (3, 2), (2, 3),
]

# Ensure consecutive cities have direct flights
for i in range(4):
    a = order[i]
    b = order[i+1]
    conditions = [z3.And(a == x, b == y) for x, y in allowed_flights]
    solver.add(z3.Or(*conditions))

# Geneva must include day 1 and day 7
for j in range(5):
    solver.add(z3.Implies(order[j] == 0, z3.And(start[j] <= 1, end[j] >= 7)))

# Oslo must include at least one day between day 19 and 23
for k in range(5):
    solver.add(z3.Implies(order[k] == 2, z3.And(start[k] <= 23, end[k] >= 19)))

# Check if a solution exists
if solver.check() == z3.sat:
    model = solver.model()
    order_vals = [model.eval(order[i]).as_long() for i in range(5)]
    start_vals = [model.eval(start[i]).as_long() for i in range(5)]
    end_vals = [model.eval(end[i]).as_long() for i in range(5)]

    # Map city numbers to names
    city_names = {0: 'Geneva', 1: 'Paris', 2: 'Oslo', 3: 'Porto', 4: 'Reykjavik'}

    # Build the itinerary
    itinerary = []
    for i in range(5):
        city = order_vals[i]
        s = start_vals[i]
        e = end_vals[i]
        for day in range(s, e + 1):
            itinerary.append({day: city_names[city]})

    # Sort by day
    itinerary.sort(key=lambda x: list(x.keys())[0])

    # Format as JSON
    json_output = {
        "itinerary": [
            {"day": list(item.keys())[0], "city": list(item.values())[0]}
            for item in itinerary
        ]
    }

    # Print the JSON output
    import json
    print(json.dumps(json_output, indent=2))
else:
    print("No solution found.")