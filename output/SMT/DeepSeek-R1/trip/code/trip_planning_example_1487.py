from z3 import *

# Define cities and their required durations
cities = {
    'Copenhagen': 5,
    'Geneva': 3,
    'Mykonos': 2,
    'Naples': 4,
    'Prague': 2,
    'Dubrovnik': 3,
    'Athens': 4,
    'Santorini': 5,
    'Brussels': 4,
    'Munich': 5
}

# Fixed date constraints
fixed = {
    'Copenhagen': (11, 15),
    'Mykonos': (27, 28),
    'Naples': (5, 8),
    'Athens': (8, 11)
}

# Direct flight pairs (bidirectional)
flight_pairs = [
    ('Copenhagen', 'Dubrovnik'), ('Dubrovnik', 'Copenhagen'),
    ('Brussels', 'Copenhagen'), ('Copenhagen', 'Brussels'),
    ('Prague', 'Geneva'), ('Geneva', 'Prague'),
    ('Athens', 'Geneva'), ('Geneva', 'Athens'),
    ('Naples', 'Dubrovnik'), ('Dubrovnik', 'Naples'),
    ('Athens', 'Dubrovnik'), ('Dubrovnik', 'Athens'),
    ('Geneva', 'Mykonos'), ('Mykonos', 'Geneva'),
    ('Naples', 'Mykonos'), ('Mykonos', 'Naples'),
    ('Naples', 'Copenhagen'), ('Copenhagen', 'Naples'),
    ('Munich', 'Mykonos'), ('Mykonos', 'Munich'),
    ('Naples', 'Athens'), ('Athens', 'Naples'),
    ('Prague', 'Athens'), ('Athens', 'Prague'),
    ('Santorini', 'Geneva'), ('Geneva', 'Santorini'),
    ('Athens', 'Santorini'), ('Santorini', 'Athens'),
    ('Naples', 'Munich'), ('Munich', 'Naples'),
    ('Prague', 'Copenhagen'), ('Copenhagen', 'Prague'),
    ('Brussels', 'Naples'), ('Naples', 'Brussels'),
    ('Athens', 'Mykonos'), ('Mykonos', 'Athens'),
    ('Athens', 'Copenhagen'), ('Copenhagen', 'Athens'),
    ('Naples', 'Geneva'), ('Geneva', 'Naples'),
    ('Dubrovnik', 'Munich'), ('Munich', 'Dubrovnik'),
    ('Brussels', 'Munich'), ('Munich', 'Brussels'),
    ('Prague', 'Brussels'), ('Brussels', 'Prague'),
    ('Brussels', 'Athens'), ('Athens', 'Brussels'),
    ('Athens', 'Munich'), ('Munich', 'Athens'),
    ('Geneva', 'Munich'), ('Munich', 'Geneva'),
    ('Copenhagen', 'Munich'), ('Munich', 'Copenhagen'),
    ('Brussels', 'Geneva'), ('Geneva', 'Brussels'),
    ('Copenhagen', 'Geneva'), ('Geneva', 'Copenhagen'),
    ('Prague', 'Munich'), ('Munich', 'Prague'),
    ('Copenhagen', 'Santorini'), ('Santorini', 'Copenhagen'),
    ('Naples', 'Santorini'), ('Santorini', 'Naples'),
    ('Geneva', 'Dubrovnik'), ('Dubrovnik', 'Geneva')
]

# Build direct_flights dictionary (one-directional)
direct_flights = {city: [] for city in cities}
for a, b in flight_pairs:
    a_fixed = a  # Assuming city names are already correctly capitalized
    b_fixed = b
    if a_fixed in cities and b_fixed in cities:
        direct_flights[a_fixed].append(b_fixed)

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

# All stays must be within 1-28 days
for city in cities:
    s.add(start[city] >= 1)
    s.add(end[city] <= 28)

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
    print("No valid trip plan exists. Check if total required days exceed 28, fixed dates overlap, or flight connections are insufficient.")