from z3 import *
import json

# Define cities and their durations
cities = ['Warsaw', 'Porto', 'Naples', 'Brussels', 'Split', 'Reykjavik', 'Amsterdam', 'Lyon', 'Helsinki', 'Valencia']
durations = {
    'Warsaw': 3,
    'Porto': 5,
    'Naples': 4,
    'Brussels': 3,
    'Split': 3,
    'Reykjavik': 5,
    'Amsterdam': 4,
    'Lyon': 3,
    'Helsinki': 4,
    'Valencia': 2
}

# Direct flights
direct_flights = {
    ('Amsterdam', 'Warsaw'), ('Helsinki', 'Brussels'), ('Helsinki', 'Warsaw'), ('Reykjavik', 'Brussels'),
    ('Amsterdam', 'Lyon'), ('Amsterdam', 'Naples'), ('Amsterdam', 'Reykjavik'), ('Naples', 'Valencia'),
    ('Porto', 'Brussels'), ('Amsterdam', 'Split'), ('Lyon', 'Split'), ('Warsaw', 'Split'), ('Porto', 'Amsterdam'),
    ('Helsinki', 'Split'), ('Brussels', 'Lyon'), ('Porto', 'Lyon'), ('Reykjavik', 'Warsaw'), ('Brussels', 'Valencia'),
    ('Valencia', 'Lyon'), ('Porto', 'Valencia'), ('Warsaw', 'Brussels'), ('Warsaw', 'Naples'), ('Naples', 'Split'),
    ('Helsinki', 'Naples'), ('Helsinki', 'Reykjavik'), ('Amsterdam', 'Valencia'), ('Naples', 'Brussels')
}

# Time constraints
time_constraints = {
    'Porto': [(1, 5)],
    'Naples': [(17, 20)],
    'Brussels': [(20, 22)],
    'Amsterdam': [(5, 8)],
    'Helsinki': [(8, 11)]
}

# Create city indices
city_indices = {city: i for i, city in enumerate(cities)}
city_durations = [durations[city] for city in cities]

# Allowed direct flight pairs as indices
allowed_pairs = set()
for (c1, c2) in direct_flights:
    idx1 = city_indices[c1]
    idx2 = city_indices[c2]
    allowed_pairs.add((idx1, idx2))
    allowed_pairs.add((idx2, idx1))  # Add reverse

# Z3 solver
solver = Solver()

# Define sequence of cities (each is an index)
seq = [Int(f'seq_{i}') for i in range(10)]

# Constraints: each city appears exactly once
for i in range(10):
    solver.add(seq[i] >= 0, seq[i] < 10)
solver.add(Distinct(seq))

# Define start and end days for each position
start_days = [Int(f'start_{i}') for i in range(10)]
end_days = [Int(f'end_{i}') for i in range(10)]

# First day is 1
solver.add(start_days[0] == 1)

# Start day of position i is end day of position i-1
for i in range(1, 10):
    solver.add(start_days[i] == end_days[i-1])

# End day is start day + duration - 1
for i in range(10):
    duration = 0
    for idx, dur in enumerate(city_durations):
        duration += If(seq[i] == idx, dur, 0)
    solver.add(end_days[i] == start_days[i] + duration - 1)

# Last end day is 27
solver.add(end_days[9] == 27)

# Add time constraints
for city, ranges in time_constraints.items():
    city_idx = city_indices[city]
    for (a, b) in ranges:
        for i in range(10):
            # If the city is at position i, then start_days[i] <= b and end_days[i] >= a
            solver.add(Implies(seq[i] == city_idx, And(start_days[i] <= b, end_days[i] >= a)))

# Add direct flight constraints between consecutive cities
for i in range(9):
    current = seq[i]
    next_city = seq[i+1]
    # Check if (current, next_city) is in allowed_pairs
    disjunction = []
    for (idx1, idx2) in allowed_pairs:
        disjunction.append(And(current == idx1, next_city == idx2))
    solver.add(Or(disjunction))

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    # Extract the sequence
    seq_values = [model.evaluate(seq[i]).as_long() for i in range(10)]
    # Extract start and end days
    start_values = [model.evaluate(start_days[i]).as_long() for i in range(10)]
    end_values = [model.evaluate(end_days[i]).as_long() for i in range(10)]
    # Build the itinerary
    itinerary = []
    for i in range(10):
        city_name = cities[seq_values[i]]
        start_day = start_values[i]
        end_day = end_values[i]
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city_name})
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")