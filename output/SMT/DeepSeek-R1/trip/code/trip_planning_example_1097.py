from z3 import *

# Define cities and their required durations
cities = {
    'Reykjavik': 4,
    'Riga': 2,
    'Oslo': 3,
    'Lyon': 5,
    'Dubrovnik': 2,
    'Madrid': 2,
    'Warsaw': 4,
    'London': 3
}

# Fixed date constraints
fixed = {
    'Riga': (4, 5),
    'Dubrovnik': (7, 8)
}

# Direct flight pairs (directional)
flight_pairs = [
    ('Warsaw', 'Reykjavik'),
    ('Oslo', 'Madrid'),
    ('Warsaw', 'Riga'),
    ('Lyon', 'London'),
    ('Madrid', 'London'),
    ('Warsaw', 'London'),
    ('Reykjavik', 'Madrid'),
    ('Warsaw', 'Oslo'),
    ('Oslo', 'Dubrovnik'),
    ('Oslo', 'Reykjavik'),
    ('Riga', 'Oslo'),
    ('Oslo', 'Lyon'),
    ('Oslo', 'London'),
    ('London', 'Reykjavik'),
    ('Warsaw', 'Madrid'),
    ('Madrid', 'Lyon'),
    ('Dubrovnik', 'Madrid')
]

# Build direct_flights dictionary (one-directional)
direct_flights = {city: [] for city in cities}
for a, b in flight_pairs:
    if a in cities and b in cities:
        direct_flights[a].append(b)

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

# All stays must be within 1-18 days
for city in cities:
    s.add(start[city] >= 1)
    s.add(end[city] <= 18)

# No overlapping stays between any two cities
for c1 in cities:
    for c2 in cities:
        if c1 != c2:
            s.add(Or(end[c1] < start[c2], end[c2] < start[c1]))

# Ensure consecutive cities in schedule order have direct flight from current to next
ordered_cities = sorted(cities.keys(), key=lambda x: start[x])
for i in range(len(ordered_cities) - 1):
    current = ordered_cities[i]
    next_city = ordered_cities[i+1]
    s.add(Or([next_city in direct_flights[current]]))

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
    print("No valid trip plan exists. Check if total required days exceed 18 or flight connections are insufficient.")