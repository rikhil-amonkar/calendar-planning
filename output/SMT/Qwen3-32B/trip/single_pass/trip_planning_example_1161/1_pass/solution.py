from z3 import *
import json

# Define the cities and their required durations
cities = ['Oslo', 'Dubrovnik', 'Helsinki', 'Vilnius', 'Krakow', 'Paris', 'Madrid', 'Mykonos']
durations = {
    'Oslo': 2,
    'Dubrovnik': 3,
    'Helsinki': 2,
    'Vilnius': 2,
    'Krakow': 5,
    'Paris': 2,
    'Madrid': 5,
    'Mykonos': 4
}

# Define direct flights as a set of tuples
direct_flights = {
    ('Oslo', 'Krakow'),
    ('Oslo', 'Paris'),
    ('Paris', 'Madrid'),
    ('Helsinki', 'Vilnius'),
    ('Oslo', 'Madrid'),
    ('Oslo', 'Helsinki'),
    ('Helsinki', 'Krakow'),
    ('Dubrovnik', 'Helsinki'),
    ('Dubrovnik', 'Madrid'),
    ('Oslo', 'Dubrovnik'),
    ('Krakow', 'Paris'),
    ('Madrid', 'Mykonos'),
    ('Oslo', 'Vilnius'),
    ('Krakow', 'Vilnius'),
    ('Helsinki', 'Paris'),
    ('Vilnius', 'Paris'),
    ('Helsinki', 'Madrid'),
}

# Map cities to indices
city_to_idx = {city: i for i, city in enumerate(cities)}
idx_to_city = {i: city for i, city in enumerate(cities)}

# Convert direct flights to index pairs (bidirectional)
direct_flight_indices = set()
for (a, b) in direct_flights:
    idx_a = city_to_idx[a]
    idx_b = city_to_idx[b]
    direct_flight_indices.add((idx_a, idx_b))
    direct_flight_indices.add((idx_b, idx_a))

# Z3 solver
s = Solver()

# Sequence of cities (indices)
sequence = [Int(f'seq_{i}') for i in range(8)]
# Starting day of each city in the sequence
starting_days = [Int(f'start_{i}') for i in range(8)]

# Constraints
# 1. Sequence is a permutation of 0-7
s.add(Distinct(sequence))
for i in range(8):
    s.add(And(0 <= sequence[i], sequence[i] < 8))

# 2. First city is Oslo (index 0)
oslo_idx = city_to_idx['Oslo']
s.add(sequence[0] == oslo_idx)

# 3. Starting day of first city is 1
s.add(starting_days[0] == 1)

# 4. Compute starting days for subsequent cities
for i in range(1, 8):
    prev_city = sequence[i-1]
    prev_duration = durations[idx_to_city[prev_city]]
    s.add(starting_days[i] == starting_days[i-1] + prev_duration - 1)

# 5. Dubrovnik's starting day is 2
dubrovnik_idx = city_to_idx['Dubrovnik']
for i in range(8):
    s.add(If(sequence[i] == dubrovnik_idx, starting_days[i] == 2, True))

# 6. Mykonos's starting day is 15
mykonos_idx = city_to_idx['Mykonos']
for i in range(8):
    s.add(If(sequence[i] == mykonos_idx, starting_days[i] == 15, True))

# 7. Consecutive cities have direct flights
for i in range(7):
    prev = sequence[i]
    next_city = sequence[i+1]
    allowed = []
    for a, b in direct_flight_indices:
        allowed.append(And(prev == a, next_city == b))
    s.add(Or(allowed))

# Check if the problem is satisfiable
if s.check() == sat:
    m = s.model()
    # Extract the sequence of city indices
    seq = [m.evaluate(sequence[i]).as_long() for i in range(8)]
    # Convert to city names
    itinerary_cities = [idx_to_city[seq[i]] for i in range(8)]
    # Extract starting days
    start_days = [m.evaluate(starting_days[i]).as_long() for i in range(8)]

    # Generate day-by-day itinerary
    itinerary = []
    for i in range(8):
        city = itinerary_cities[i]
        start = start_days[i]
        duration = durations[city]
        for day in range(start, start + duration):
            itinerary.append({"day": day, "city": city})

    # Sort by day (already in order)
    itinerary.sort(key=lambda x: x['day'])

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")