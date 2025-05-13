from z3 import *

# Define cities and their required durations
cities = {
    'Porto': 2,
    'Geneva': 3,
    'Mykonos': 3,
    'Manchester': 4,
    'Hamburg': 5,
    'Naples': 5,
    'Frankfurt': 2
}

# Fixed date constraints
fixed = {
    'Mykonos': (10, 12),
    'Manchester': (15, 18),
    'Frankfurt': (5, 6)
}

# Direct flight pairs (note unidirectional Hamburg→Geneva)
flight_pairs = [
    ('Hamburg', 'Frankfurt'), ('Frankfurt', 'Hamburg'),
    ('Naples', 'Mykonos'), ('Mykonos', 'Naples'),
    ('Hamburg', 'Porto'), ('Porto', 'Hamburg'),
    ('Hamburg', 'Geneva'),  # Unidirectional
    ('Mykonos', 'Geneva'), ('Geneva', 'Mykonos'),
    ('Frankfurt', 'Geneva'), ('Geneva', 'Frankfurt'),
    ('Frankfurt', 'Porto'), ('Porto', 'Frankfurt'),
    ('Geneva', 'Porto'), ('Porto', 'Geneva'),
    ('Geneva', 'Manchester'), ('Manchester', 'Geneva'),
    ('Naples', 'Manchester'), ('Manchester', 'Naples'),
    ('Frankfurt', 'Naples'), ('Naples', 'Frankfurt'),
    ('Frankfurt', 'Manchester'), ('Manchester', 'Frankfurt'),
    ('Naples', 'Geneva'), ('Geneva', 'Naples'),
    ('Porto', 'Manchester'), ('Manchester', 'Porto'),
    ('Hamburg', 'Manchester'), ('Manchester', 'Hamburg')
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
    print("No valid trip plan exists. Check if total required days exceed 18, fixed dates overlap, or flight connections are insufficient.")