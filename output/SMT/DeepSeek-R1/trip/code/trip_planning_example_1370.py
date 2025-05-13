from z3 import *

# Define cities and their required durations
cities = {
    'Santorini': 5,
    'Krakow': 5,
    'Paris': 5,
    'Vilnius': 3,
    'Munich': 5,
    'Geneva': 2,
    'Amsterdam': 4,
    'Budapest': 5,
    'Split': 4
}

# Fixed date constraints
fixed = {
    'Santorini': (25, 29),
    'Krakow': (18, 22),
    'Paris': (11, 15)
}

# Direct flight pairs (directional)
flight_pairs = [
    ('Paris', 'Krakow'), ('Krakow', 'Paris'),
    ('Paris', 'Amsterdam'), ('Amsterdam', 'Paris'),
    ('Paris', 'Split'), ('Split', 'Paris'),
    ('Vilnius', 'Munich'),
    ('Paris', 'Geneva'), ('Geneva', 'Paris'),
    ('Amsterdam', 'Geneva'), ('Geneva', 'Amsterdam'),
    ('Munich', 'Split'), ('Split', 'Munich'),
    ('Split', 'Krakow'), ('Krakow', 'Split'),
    ('Munich', 'Amsterdam'), ('Amsterdam', 'Munich'),
    ('Budapest', 'Amsterdam'), ('Amsterdam', 'Budapest'),
    ('Split', 'Geneva'), ('Geneva', 'Split'),
    ('Vilnius', 'Split'), ('Split', 'Vilnius'),
    ('Munich', 'Geneva'), ('Geneva', 'Munich'),
    ('Munich', 'Krakow'), ('Krakow', 'Munich'),
    ('Krakow', 'Vilnius'),
    ('Vilnius', 'Amsterdam'), ('Amsterdam', 'Vilnius'),
    ('Budapest', 'Paris'), ('Paris', 'Budapest'),
    ('Krakow', 'Amsterdam'), ('Amsterdam', 'Krakow'),
    ('Vilnius', 'Paris'), ('Paris', 'Vilnius'),
    ('Budapest', 'Geneva'), ('Geneva', 'Budapest'),
    ('Split', 'Amsterdam'), ('Amsterdam', 'Split'),
    ('Santorini', 'Geneva'), ('Geneva', 'Santorini'),
    ('Amsterdam', 'Santorini'), ('Santorini', 'Amsterdam'),
    ('Munich', 'Budapest'), ('Budapest', 'Munich'),
    ('Munich', 'Paris'), ('Paris', 'Munich')
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

# All stays must be within 1-30 days
for city in cities:
    s.add(start[city] >= 1)
    s.add(end[city] <= 30)

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
    print("No valid trip plan exists. Check if total required days exceed 30 or flight connections are insufficient.")