from z3 import *

# Define cities and their required durations
cities = {
    'Nice': 5,
    'Krakow': 6,
    'Dublin': 7,
    'Lyon': 4,
    'Frankfurt': 2
}

# Fixed date constraints
fixed = {
    'Nice': (1, 5),
    'Frankfurt': (19, 20)
}

# Direct flight pairs (bidirectional)
flight_pairs = [
    ('Nice', 'Dublin'),
    ('Dublin', 'Frankfurt'),
    ('Dublin', 'Krakow'),
    ('Krakow', 'Frankfurt'),
    ('Lyon', 'Frankfurt'),
    ('Nice', 'Frankfurt'),
    ('Lyon', 'Dublin'),
    ('Nice', 'Lyon')
]

# Build direct_flights dictionary (bidirectional)
direct_flights = {city: [] for city in cities}
for a, b in flight_pairs:
    direct_flights[a].append(b)
    direct_flights[b].append(a)

# Create solver instance
s = Solver()

# Create start and end day variables for each city
start = {city: Int(f'start_{city}') for city in cities}
end = {city: Int(f'end_{city}') for city in cities}

# Add duration constraints
for city in cities:
    s.add(end[city] == start[city] + cities[city] - 1)

# Apply fixed date constraints
for city, (fixed_start, fixed_end) in fixed.items():
    s.add(start[city] == fixed_start)
    s.add(end[city] == fixed_end)

# All stays must be within 1-20 days
for city in cities:
    s.add(start[city] >= 1)
    s.add(end[city] <= 20)

# No overlapping stays between any two cities
for c1 in cities:
    for c2 in cities:
        if c1 != c2:
            s.add(Or(end[c1] < start[c2], end[c2] < start[c1]))

# Flight connectivity between consecutive cities
# Create ordering variables to sequence the cities
order = {city: Int(f'order_{city}') for city in cities}
for city in cities:
    s.add(order[city] >= 1, order[city] <= len(cities))

# All cities have unique order positions
s.add(Distinct([order[city] for city in cities]))

# Ensure consecutive cities in order have direct flights
for i in range(1, len(cities)):
    prev_cities = [city for city in cities if order[city] == i]
    next_cities = [city for city in cities if order[city] == i+1]
    for prev in prev_cities:
        for nxt in next_cities:
            s.add(Implies(And(order[prev] == i, order[nxt] == i+1), nxt in direct_flights[prev]))

# Check for satisfiability
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
    print("No valid trip plan exists. Total required days exceed 20 or flight connections are insufficient.")