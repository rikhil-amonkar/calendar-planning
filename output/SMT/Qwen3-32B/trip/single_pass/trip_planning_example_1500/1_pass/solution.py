from z3 import *

# Define cities and their durations
cities = ['London', 'Zurich', 'Bucharest', 'Hamburg', 'Barcelona', 'Reykjavik', 'Stuttgart', 'Stockholm', 'Tallinn', 'Milan']
durations = [3, 2, 2, 5, 4, 5, 5, 2, 4, 5]

# Define direct flights
direct_flight_pairs = [
    ('London', 'Hamburg'),
    ('London', 'Reykjavik'),
    ('Milan', 'Barcelona'),
    ('Reykjavik', 'Barcelona'),
    ('Reykjavik', 'Stuttgart'),
    ('Stockholm', 'Reykjavik'),
    ('London', 'Stuttgart'),
    ('Milan', 'Zurich'),
    ('London', 'Barcelona'),
    ('Stockholm', 'Hamburg'),
    ('Zurich', 'Barcelona'),
    ('Stockholm', 'Stuttgart'),
    ('Milan', 'Hamburg'),
    ('Stockholm', 'Tallinn'),
    ('Hamburg', 'Bucharest'),
    ('London', 'Bucharest'),
    ('Milan', 'Stockholm'),
    ('Stuttgart', 'Hamburg'),
    ('London', 'Zurich'),
    ('Milan', 'Reykjavik'),
    ('London', 'Stockholm'),
    ('Milan', 'Stuttgart'),
    ('Stockholm', 'Barcelona'),
    ('London', 'Milan'),
    ('Zurich', 'Hamburg'),
    ('Bucharest', 'Barcelona'),
    ('Zurich', 'Stockholm'),
    ('Barcelona', 'Tallinn'),
    ('Zurich', 'Tallinn'),
    ('Hamburg', 'Barcelona'),
    ('Stuttgart', 'Barcelona'),
    ('Zurich', 'Reykjavik'),
    ('Zurich', 'Bucharest'),
]

flight_set = set()
for a, b in direct_flight_pairs:
    a_idx = cities.index(a)
    b_idx = cities.index(b)
    flight_set.add((a_idx, b_idx))
    flight_set.add((b_idx, a_idx))

# Create Z3 solver
solver = Solver()

# Define sequence variables
seq = [Int(f'seq_{i}') for i in range(10)]
start = [Int(f'start_{i}') for i in range(10)]

# Add constraints for sequence
# First city is London (index 0)
solver.add(seq[0] == 0)

# All cities are distinct
for i in range(10):
    for j in range(i + 1, 10):
        solver.add(seq[i] != seq[j])

# Each city is between 0 and 9
for i in range(10):
    solver.add(And(seq[i] >= 0, seq[i] <= 9))

# Compute start days
solver.add(start[0] == 1)
for i in range(1, 10):
    prev_city = seq[i - 1]
    prev_duration = durations[prev_city]
    solver.add(start[i] == start[i - 1] + prev_duration - 1)

# Add constraints for specific cities
for i in range(10):
    city_idx = seq[i]
    # Milan (index 9) must have start <=7
    solver.add(If(city_idx == 9, start[i] <= 7, True))
    # Zurich (index 1) must have start ==7
    solver.add(If(city_idx == 1, start[i] == 7, True))
    # Reykjavik (index 5) must have 5 <= start <=13
    solver.add(If(city_idx == 5, And(start[i] >= 5, start[i] <= 13), True))

# Add flight constraints for consecutive cities
for i in range(9):
    current_city = seq[i]
    next_city = seq[i + 1]
    # Create a list of allowed pairs
    allowed = []
    for a, b in flight_set:
        allowed.append(And(current_city == a, next_city == b))
    solver.add(Or(allowed))

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    # Extract the sequence
    sequence = [model.evaluate(seq[i]).as_long() for i in range(10)]
    # Compute start days
    start_days = [model.evaluate(start[i]).as_long() for i in range(10)]
    # Generate the itinerary
    itinerary = []
    for i in range(10):
        city_idx = sequence[i]
        city_name = cities[city_idx]
        duration = durations[city_idx]
        s_day = start_days[i]
        e_day = s_day + duration - 1
        for day in range(s_day, e_day + 1):
            itinerary.append((day, city_name))
    # Sort itinerary by day
    itinerary.sort()
    # Convert to JSON format
    import json
    json_itinerary = {'itinerary': [{'day': day, 'city': city} for day, city in itinerary]}
    print(json.dumps(json_itinerary, indent=2))
else:
    print("No solution found.")