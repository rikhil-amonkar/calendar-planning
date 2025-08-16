from z3 import *

# Define cities and their required days
cities_list = ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon']
city_to_idx = {city: i for i, city in enumerate(cities_list)}

cities_required_days = {
    'Paris': 5,
    'Warsaw': 2,
    'Krakow': 2,
    'Tallinn': 2,
    'Riga': 2,
    'Copenhagen': 5,
    'Helsinki': 5,
    'Oslo': 5,
    'Santorini': 2,
    'Lyon': 4
}

# Event constraints: (city, start_day, end_day)
events = [
    ('Paris', 4, 8),
    ('Krakow', 17, 18),
    ('Riga', 23, 24),
    ('Helsinki', 18, 22),
    ('Santorini', 12, 13)
]

# Allowed direct flights
allowed_transitions_pairs = [
    ('Warsaw', 'Riga'),
    ('Warsaw', 'Tallinn'),
    ('Copenhagen', 'Helsinki'),
    ('Lyon', 'Paris'),
    ('Copenhagen', 'Warsaw'),
    ('Lyon', 'Oslo'),
    ('Paris', 'Oslo'),
    ('Paris', 'Riga'),
    ('Krakow', 'Helsinki'),
    ('Paris', 'Tallinn'),
    ('Oslo', 'Riga'),
    ('Krakow', 'Warsaw'),
    ('Paris', 'Helsinki'),
    ('Copenhagen', 'Santorini'),
    ('Helsinki', 'Warsaw'),
    ('Helsinki', 'Riga'),
    ('Copenhagen', 'Krakow'),
    ('Copenhagen', 'Riga'),
    ('Paris', 'Krakow'),
    ('Copenhagen', 'Oslo'),
    ('Oslo', 'Tallinn'),
    ('Oslo', 'Helsinki'),
    ('Copenhagen', 'Tallinn'),
    ('Oslo', 'Krakow'),
    ('Riga', 'Tallinn'),
    ('Helsinki', 'Tallinn'),
    ('Paris', 'Copenhagen'),
    ('Paris', 'Warsaw'),
    ('Santorini', 'Oslo'),
    ('Oslo', 'Warsaw'),
]

# Convert to allowed transitions with both directions
allowed_transitions = set()
for a, b in allowed_transitions_pairs:
    allowed_transitions.add((a, b))
    allowed_transitions.add((b, a))

# Convert to indices
allowed_transitions_idx = set()
for a, b in allowed_transitions:
    a_idx = city_to_idx[a]
    b_idx = city_to_idx[b]
    allowed_transitions_idx.add((a_idx, b_idx))

# Create Z3 solver
s = Solver()

# Create variables for each day (0-based index, day 0 is day 1)
days = [Int(f'day_{i+1}') for i in range(25)]

# Add constraints for each day to be a valid city index
for d in days:
    s.add(And(0 <= d, d <= 9))

# Add transition constraints between consecutive days
for i in range(24):
    current_day = days[i]
    next_day = days[i+1]
    transitions = []
    for a, b in allowed_transitions_idx:
        transitions.append(And(current_day == a, next_day == b))
    s.add(Or(transitions))

# Add count constraints for each city
for city_idx in range(10):
    city_name = cities_list[city_idx]
    required_days = cities_required_days[city_name]
    total_days = Sum([If(day == city_idx, 1, 0) for day in days])
    s.add(total_days == required_days)

# Add event constraints
for event in events:
    city_name, start_day, end_day = event
    city_idx = city_to_idx[city_name]
    constraints = []
    for day_num in range(start_day, end_day + 1):
        idx = day_num - 1  # days are 0-based in the list
        constraints.append(days[idx] == city_idx)
    s.add(Or(constraints))

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(25):
        day_num = i + 1
        city_idx = model[days[i]].as_long()
        city_name = cities_list[city_idx]
        itinerary.append({'day': day_num, 'city': city_name})
    # Output as JSON
    import json
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print("No solution found.")