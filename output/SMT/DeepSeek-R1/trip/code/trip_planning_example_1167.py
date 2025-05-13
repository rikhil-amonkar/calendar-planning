from z3 import *

# Define cities and their required durations
cities = {
    'Dublin': 5,
    'Krakow': 4,
    'Istanbul': 3,
    'Venice': 3,
    'Naples': 4,
    'Brussels': 2,
    'Mykonos': 4,
    'Frankfurt': 3
}

# Fixed date constraints
fixed = {
    'Dublin': (11, 15),
    'Istanbul': (9, 11),
    'Mykonos': (1, 4),
    'Frankfurt': (15, 17)
}

# Direct flight pairs (note unidirectional Brussels→Frankfurt)
flight_pairs = [
    ('Dublin', 'Brussels'), ('Brussels', 'Dublin'),
    ('Mykonos', 'Naples'), ('Naples', 'Mykonos'),
    ('Venice', 'Istanbul'), ('Istanbul', 'Venice'),
    ('Frankfurt', 'Krakow'), ('Krakow', 'Frankfurt'),
    ('Naples', 'Dublin'), ('Dublin', 'Naples'),
    ('Krakow', 'Brussels'), ('Brussels', 'Krakow'),
    ('Naples', 'Istanbul'), ('Istanbul', 'Naples'),
    ('Naples', 'Brussels'), ('Brussels', 'Naples'),
    ('Istanbul', 'Frankfurt'), ('Frankfurt', 'Istanbul'),
    ('Brussels', 'Frankfurt'),  # Unidirectional
    ('Istanbul', 'Krakow'), ('Krakow', 'Istanbul'),
    ('Istanbul', 'Brussels'), ('Brussels', 'Istanbul'),
    ('Venice', 'Frankfurt'), ('Frankfurt', 'Venice'),
    ('Naples', 'Frankfurt'), ('Frankfurt', 'Naples'),
    ('Dublin', 'Krakow'), ('Krakow', 'Dublin'),
    ('Venice', 'Brussels'), ('Brussels', 'Venice'),
    ('Naples', 'Venice'), ('Venice', 'Naples'),
    ('Istanbul', 'Dublin'), ('Dublin', 'Istanbul'),
    ('Venice', 'Dublin'), ('Dublin', 'Venice'),
    ('Dublin', 'Frankfurt'), ('Frankfurt', 'Dublin')
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

# All stays must be within 1-21 days
for city in cities:
    s.add(start[city] >= 1)
    s.add(end[city] <= 21)

# No overlapping stays between any two cities
for c1 in cities:
    for c2 in cities:
        if c1 != c2:
            s.add(Or(end[c1] < start[c2], end[c2] < start[c1]))

# Flight connectivity constraints using order variables
order = {city: Int(f'order_{city}') for city in cities}
for city in cities:
    s.add(order[city] >= 1, order[city] <= len(cities))

# All order values must be distinct
s.add(Distinct([order[city] for city in cities]))

# Ensure consecutive cities in order have direct flight from current to next
for c1 in cities:
    for c2 in cities:
        if c1 != c2:
            s.add(Implies(order[c1] + 1 == order[c2], Or([c2 in direct_flights[c1]])))

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
    print("No valid trip plan exists. Check if total required days exceed 21, fixed dates overlap, or flight connections are insufficient.")