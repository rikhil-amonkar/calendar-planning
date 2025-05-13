from z3 import *

# Define cities and their required durations
cities = {
    'Vienna': 4,
    'Lyon': 3,
    'Edinburgh': 4,
    'Reykjavik': 5,
    'Stuttgart': 5,
    'Manchester': 2,
    'Split': 5,
    'Prague': 4
}

# Fixed date constraints
fixed = {
    'Edinburgh': (5, 8),
    'Split': (19, 23)
}

# Direct flight pairs (directional)
flight_pairs = [
    ('Reykjavik', 'Stuttgart'),
    ('Stuttgart', 'Split'),
    ('Split', 'Stuttgart'),
    ('Stuttgart', 'Vienna'),
    ('Vienna', 'Stuttgart'),
    ('Prague', 'Manchester'),
    ('Manchester', 'Prague'),
    ('Edinburgh', 'Prague'),
    ('Prague', 'Edinburgh'),
    ('Manchester', 'Split'),
    ('Prague', 'Vienna'),
    ('Vienna', 'Prague'),
    ('Vienna', 'Manchester'),
    ('Manchester', 'Vienna'),
    ('Prague', 'Split'),
    ('Split', 'Prague'),
    ('Vienna', 'Lyon'),
    ('Lyon', 'Vienna'),
    ('Stuttgart', 'Edinburgh'),
    ('Edinburgh', 'Stuttgart'),
    ('Split', 'Lyon'),
    ('Lyon', 'Split'),
    ('Stuttgart', 'Manchester'),
    ('Manchester', 'Stuttgart'),
    ('Prague', 'Lyon'),
    ('Lyon', 'Prague'),
    ('Reykjavik', 'Vienna'),
    ('Vienna', 'Reykjavik'),
    ('Prague', 'Reykjavik'),
    ('Reykjavik', 'Prague'),
    ('Vienna', 'Split'),
    ('Split', 'Vienna')
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

# All stays must be within 1-25 days
for city in cities:
    s.add(start[city] >= 1)
    s.add(end[city] <= 25)

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
    print("No valid trip plan exists. Check if total required days exceed 25 or flight connections are insufficient.")