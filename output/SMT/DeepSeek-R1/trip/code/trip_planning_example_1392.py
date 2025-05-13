from z3 import *

# Define cities and their required durations
cities = {
    'Naples': 3,
    'Valencia': 5,
    'Stuttgart': 2,
    'Split': 5,
    'Venice': 5,
    'Amsterdam': 4,
    'Nice': 2,
    'Barcelona': 2,
    'Porto': 4
}

# Fixed date constraints
fixed = {
    'Venice': (6, 10),
    'Barcelona': (5, 6),
    'Naples': (18, 20),
    'Nice': (23, 24)
}

# Direct flight pairs (bidirectional)
flight_pairs = [
    ('Venice', 'Nice'),
    ('Naples', 'Amsterdam'),
    ('Barcelona', 'Nice'),
    ('Amsterdam', 'Nice'),
    ('Stuttgart', 'Valencia'),
    ('Stuttgart', 'Porto'),
    ('Split', 'Stuttgart'),
    ('Split', 'Naples'),
    ('Valencia', 'Amsterdam'),
    ('Barcelona', 'Porto'),
    ('Valencia', 'Naples'),
    ('Venice', 'Amsterdam'),
    ('Barcelona', 'Naples'),
    ('Barcelona', 'Valencia'),
    ('Split', 'Amsterdam'),
    ('Barcelona', 'Venice'),
    ('Stuttgart', 'Amsterdam'),
    ('Naples', 'Nice'),
    ('Venice', 'Stuttgart'),
    ('Split', 'Barcelona'),
    ('Porto', 'Nice'),
    ('Barcelona', 'Stuttgart'),
    ('Venice', 'Naples'),
    ('Porto', 'Amsterdam'),
    ('Porto', 'Valencia'),
    ('Stuttgart', 'Naples'),
    ('Barcelona', 'Amsterdam')
]

# Build direct_flights dictionary
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

# All stays must be within 1-24 days
for city in cities:
    s.add(start[city] >= 1)
    s.add(end[city] <= 24)

# No overlapping stays between any two cities
for c1 in cities:
    for c2 in cities:
        if c1 != c2:
            s.add(Or(end[c1] < start[c2], end[c2] < start[c1]))

# Ensure consecutive cities in schedule order have direct flights
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
    print("No valid trip plan exists. Check if total required days exceed 24 or flight connections are insufficient.")