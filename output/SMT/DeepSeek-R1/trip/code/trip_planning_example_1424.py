from z3 import *

# Define cities and their required durations
cities = {
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

# Fixed dates
fixed = {
    'Porto': (1, 5),
    'Amsterdam': (5, 8),
    'Helsinki': (8, 11),
    'Naples': (17, 20),
    'Brussels': (20, 22)
}

# Direct flight pairs (bidirectional)
flight_pairs = [
    ('Amsterdam', 'Warsaw'),
    ('Helsinki', 'Brussels'),
    ('Helsinki', 'Warsaw'),
    ('Reykjavik', 'Brussels'),
    ('Amsterdam', 'Lyon'),
    ('Amsterdam', 'Naples'),
    ('Amsterdam', 'Reykjavik'),
    ('Naples', 'Valencia'),
    ('Porto', 'Brussels'),
    ('Amsterdam', 'Split'),
    ('Lyon', 'Split'),
    ('Warsaw', 'Split'),
    ('Porto', 'Amsterdam'),
    ('Helsinki', 'Split'),
    ('Brussels', 'Lyon'),
    ('Porto', 'Lyon'),
    ('Reykjavik', 'Warsaw'),
    ('Brussels', 'Valencia'),
    ('Valencia', 'Lyon'),
    ('Porto', 'Warsaw'),
    ('Warsaw', 'Valencia'),
    ('Amsterdam', 'Helsinki'),
    ('Porto', 'Valencia'),
    ('Warsaw', 'Naples'),
    ('Naples', 'Split'),
    ('Helsinki', 'Naples'),
    ('Helsinki', 'Reykjavik'),
    ('Amsterdam', 'Valencia'),
    ('Naples', 'Brussels'),
]

# Build direct_flights dictionary
direct_flights = {city: [] for city in cities}
for a, b in flight_pairs:
    a_fixed = a if a != 'Helsinki' else 'Helsinki'  # Correct typo in pair
    b_fixed = b if b != 'Helsinki' else 'Helsinki'
    if a_fixed in cities and b_fixed in cities:
        direct_flights[a_fixed].append(b_fixed)
        direct_flights[b_fixed].append(a_fixed)

# Create solver
s = Solver()

# Create start and end day variables for each city
start = {city: Int(f'start_{city}') for city in cities}
end = {city: Int(f'end_{city}') for city in cities}

# Add duration constraints
for city in cities:
    s.add(end[city] == start[city] + cities[city] - 1)

# Fixed dates constraints
for city, (fixed_start, fixed_end) in fixed.items():
    s.add(start[city] == fixed_start)
    s.add(end[city] == fixed_end)

# All cities have valid start and end days
for city in cities:
    s.add(start[city] >= 1)
    s.add(end[city] <= 27)

# No overlapping stays
for c1 in cities:
    for c2 in cities:
        if c1 != c2:
            s.add(Or(end[c1] < start[c2], end[c2] < start[c1]))

# Ensure flight connectivity between consecutive cities
# Order cities by start day
order = sorted(cities.keys(), key=lambda x: start[x])

# Consecutive cities must have a direct flight
for i in range(len(order) - 1):
    current = order[i]
    next_city = order[i + 1]
    s.add(Or([next_city in direct_flights[current], current in direct_flights[next_city]))

# Check satisfiability
if s.check() == sat:
    m = s.model()
    schedule = []
    for city in cities:
        schedule.append((city, m.eval(start[city]).as_long(), m.eval(end[city]).as_long()))
    schedule.sort(key=lambda x: x[1])
    print("Valid trip plan:")
    for entry in schedule:
        print(f"{entry[0]}: Days {entry[1]} to {entry[2]}")
else:
    print("No valid trip plan exists.")