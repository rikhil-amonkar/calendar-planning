import z3
import json

# Initialize Z3 solver
solver = z3.Solver()

# Define cities as variables (0: Seville, 1: Rome, 2: Istanbul, 3: Naples, 4: Santorini)
cities = [z3.Int(f'c{i}') for i in range(5)]

# Allowed transitions between cities
allowed_pairs = [
    (0, 1), (1, 0), (1, 4), (4, 1), (1, 3), (3, 1),
    (1, 2), (2, 1), (2, 3), (3, 2), (3, 4), (4, 3)
]

# Constraints: all cities are distinct and within range
solver.add(z3.Distinct(cities))
solver.add(z3.And([z3.And(0 <= c, c <= 4) for c in cities]))

# Ensure allowed transitions between consecutive cities
for i in range(4):
    current = cities[i]
    next_c = cities[i + 1]
    constraints = []
    for a, b in allowed_pairs:
        constraints.append(z3.And(current == a, next_c == b))
    solver.add(z3.Or(constraints))

# Define start and end days for each city in the sequence
start_days = [z3.Int(f's{i}') for i in range(5)]
end_days = [z3.Int(f'e{i}') for i in range(5)]

# Required days for each city [Seville, Rome, Istanbul, Naples, Santorini]
required_days = [4, 3, 2, 7, 4]

# Compute durations and set start/end day constraints
for i in range(5):
    duration_i = z3.If(cities[i] == 0, 4,
        z3.If(cities[i] == 1, 3,
            z3.If(cities[i] == 2, 2,
                z3.If(cities[i] == 3, 7, 4))))
    if i == 0:
        solver.add(start_days[i] == 1)
    else:
        solver.add(start_days[i] == end_days[i - 1])
    solver.add(end_days[i] == start_days[i] + duration_i - 1)

# Constraints for Istanbul (must include day 6 and 7)
for i in range(5):
    solver.add(z3.Implies(cities[i] == 2, z3.And(start_days[i] <= 6, end_days[i] >= 7)))

# Constraints for Santorini (must include at least one day between 13-16)
for i in range(5):
    solver.add(z3.Implies(cities[i] == 4, z3.And(start_days[i] <= 16, end_days[i] >= 13)))

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    city_sequence = [model[cities[i]].as_long() for i in range(5)]
    start_days_vals = [model[start_days[i]].as_long() for i in range(5)]
    end_days_vals = [model[end_days[i]].as_long() for i in range(5)]
    
    city_names = ['Seville', 'Rome', 'Istanbul', 'Naples', 'Santorini']
    itinerary = []
    for i in range(5):
        city_code = city_sequence[i]
        city_name = city_names[city_code]
        s = start_days_vals[i]
        e = end_days_vals[i]
        for day in range(s, e + 1):
            itinerary.append({'day': day, 'city': city_name})
    
    # Sort itinerary by day (though already in order)
    itinerary.sort(key=lambda x: x['day'])
    
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print("No solution found.")