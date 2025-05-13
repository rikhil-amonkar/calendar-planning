from z3 import *

# Define cities and their required durations
cities = {
    'Vienna': 4,
    'Barcelona': 2,
    'Edinburgh': 4,
    'Krakow': 3,
    'Riga': 4,
    'Hamburg': 2,
    'Paris': 2,
    'Stockholm': 2
}

# Fixed date constraints
fixed = {
    'Paris': (1, 2),
    'Hamburg': (10, 11),
    'Edinburgh': (12, 15),
    'Stockholm': (15, 16)
}

# Direct flight pairs (note unidirectional Riga→Hamburg)
flight_pairs = [
    ('Hamburg', 'Stockholm'), ('Stockholm', 'Hamburg'),
    ('Vienna', 'Stockholm'), ('Stockholm', 'Vienna'),
    ('Paris', 'Edinburgh'), ('Edinburgh', 'Paris'),
    ('Riga', 'Barcelona'), ('Barcelona', 'Riga'),
    ('Paris', 'Riga'), ('Riga', 'Paris'),
    ('Krakow', 'Barcelona'), ('Barcelona', 'Krakow'),
    ('Edinburgh', 'Stockholm'), ('Stockholm', 'Edinburgh'),
    ('Paris', 'Krakow'), ('Krakow', 'Paris'),
    ('Krakow', 'Stockholm'), ('Stockholm', 'Krakow'),
    ('Riga', 'Edinburgh'), ('Edinburgh', 'Riga'),
    ('Barcelona', 'Stockholm'), ('Stockholm', 'Barcelona'),
    ('Paris', 'Stockholm'), ('Stockholm', 'Paris'),
    ('Krakow', 'Edinburgh'), ('Edinburgh', 'Krakow'),
    ('Vienna', 'Hamburg'), ('Hamburg', 'Vienna'),
    ('Paris', 'Hamburg'), ('Hamburg', 'Paris'),
    ('Riga', 'Stockholm'), ('Stockholm', 'Riga'),
    ('Hamburg', 'Barcelona'), ('Barcelona', 'Hamburg'),
    ('Vienna', 'Barcelona'), ('Barcelona', 'Vienna'),
    ('Krakow', 'Vienna'), ('Vienna', 'Krakow'),
    ('Riga', 'Hamburg'),  # Unidirectional flight
    ('Barcelona', 'Edinburgh'), ('Edinburgh', 'Barcelona'),
    ('Paris', 'Barcelona'), ('Barcelona', 'Paris'),
    ('Hamburg', 'Edinburgh'), ('Edinburgh', 'Hamburg'),
    ('Paris', 'Vienna'), ('Vienna', 'Paris'),
    ('Vienna', 'Riga'), ('Riga', 'Vienna')
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

# All stays must be within 1-16 days
for city in cities:
    s.add(start[city] >= 1)
    s.add(end[city] <= 16)

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
    print("No valid trip plan exists. Check if total required days exceed 16, fixed dates overlap, or flight connections are insufficient.")