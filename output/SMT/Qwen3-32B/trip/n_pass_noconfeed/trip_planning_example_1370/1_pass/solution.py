import z3
import json

# Define cities and their durations
cities = ['Santorini', 'Krakow', 'Paris', 'Vilnius', 'Munich', 'Geneva', 'Amsterdam', 'Budapest', 'Split']
city_to_index = {city: idx for idx, city in enumerate(cities)}
durations = [5, 5, 5, 3, 5, 2, 4, 5, 4]  # durations for each city index

# Direct flights as per problem statement
direct_flights = [
    ('Paris', 'Krakow'),
    ('Paris', 'Amsterdam'),
    ('Paris', 'Split'),
    ('Vilnius', 'Munich'),
    ('Paris', 'Geneva'),
    ('Amsterdam', 'Geneva'),
    ('Munich', 'Split'),
    ('Split', 'Krakow'),
    ('Munich', 'Amsterdam'),
    ('Budapest', 'Amsterdam'),
    ('Split', 'Geneva'),
    ('Vilnius', 'Split'),
    ('Munich', 'Geneva'),
    ('Munich', 'Krakow'),
    ('Krakow', 'Vilnius'),
    ('Vilnius', 'Amsterdam'),
    ('Budapest', 'Paris'),
    ('Krakow', 'Amsterdam'),
    ('Vilnius', 'Paris'),
    ('Budapest', 'Geneva'),
    ('Split', 'Amsterdam'),
    ('Santorini', 'Geneva'),
    ('Amsterdam', 'Santorini'),
    ('Munich', 'Budapest'),
    ('Munich', 'Paris'),
]

# Generate allowed transitions as set of (from, to) index pairs
allowed_transitions = set()
for a, b in direct_flights:
    a_idx = city_to_index[a]
    b_idx = city_to_index[b]
    allowed_transitions.add((a_idx, b_idx))
    allowed_transitions.add((b_idx, a_idx))
allowed_transitions = list(allowed_transitions)

# Create Z3 solver
s = z3.Solver()

# Create variables for sequence of cities (seq[0] to seq[8])
seq = [z3.Int(f'seq_{i}') for i in range(9)]

# Add constraints: each city appears exactly once
s.add(z3.Distinct(seq))
for city in seq:
    s.add(z3.And(0 <= city, city <= 8))

# Add constraints for allowed transitions between consecutive cities
for i in range(8):  # 0 to 7
    transitions = []
    for (from_city, to_city) in allowed_transitions:
        transitions.append(z3.And(seq[i] == from_city, seq[i+1] == to_city))
    s.add(z3.Or(transitions))

# Create variables for start days of each city in the sequence
start = [z3.Int(f'start_{i}') for i in range(9)]

# Add constraints for start days
s.add(start[0] == 1)
for i in range(1, 9):
    prev_city = seq[i-1]
    duration_prev = z3.If(prev_city == 0, 5,
        z3.If(prev_city == 1, 5,
        z3.If(prev_city == 2, 5,
        z3.If(prev_city == 3, 3,
        z3.If(prev_city == 4, 5,
        z3.If(prev_city == 5, 2,
        z3.If(prev_city == 6, 4,
        z3.If(prev_city == 7, 5, 4))))))))
    s.add(start[i] == start[i-1] + duration_prev - 1)

# Add time constraints for Santorini (0), Krakow (1), Paris (2)
for j in range(9):
    # Santorini (index 0)
    s.add(z3.Implies(seq[j] == 0, z3.And(21 <= start[j], start[j] <= 29)))
    # Krakow (index 1)
    s.add(z3.Implies(seq[j] == 1, z3.And(14 <= start[j], start[j] <= 22)))
    # Paris (index 2)
    s.add(z3.Implies(seq[j] == 2, z3.And(7 <= start[j], start[j] <= 15)))

# Check if the solver can find a solution
if s.check() == z3.sat:
    model = s.model()
    # Extract the sequence
    sequence = [model.evaluate(seq[i]).as_long() for i in range(9)]
    # Extract the start days
    start_days = [model.evaluate(start[i]).as_long() for i in range(9)]
    # Generate the itinerary
    itinerary = []
    for i in range(9):
        city_idx = sequence[i]
        city_name = cities[city_idx]
        duration = durations[city_idx]
        start_day = start_days[i]
        end_day = start_day + duration - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city_name})
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"error": "No solution found"}))