from z3 import *

# Define cities and their required durations
cities = {
    'Prague': 5,
    'Brussels': 2,
    'Riga': 2,
    'Munich': 2,
    'Seville': 3,
    'Stockholm': 2,
    'Istanbul': 2,
    'Amsterdam': 3,
    'Vienna': 5,
    'Split': 3
}

# Fixed date constraints
fixed = {
    'Vienna': (1, 5),
    'Prague': (5, 9),
    'Split': (11, 13),
    'Riga': (15, 16),
    'Stockholm': (16, 17)
}

# Direct flight pairs (bidirectional)
flight_pairs = [
    ('Riga', 'Stockholm'), ('Stockholm', 'Riga'),
    ('Stockholm', 'Brussels'), ('Brussels', 'Stockholm'),
    ('Istanbul', 'Munich'), ('Munich', 'Istanbul'),
    ('Istanbul', 'Riga'), ('Riga', 'Istanbul'),
    ('Prague', 'Split'), ('Split', 'Prague'),
    ('Vienna', 'Brussels'), ('Brussels', 'Vienna'),
    ('Vienna', 'Riga'), ('Riga', 'Vienna'),
    ('Split', 'Stockholm'), ('Stockholm', 'Split'),
    ('Munich', 'Amsterdam'), ('Amsterdam', 'Munich'),
    ('Split', 'Amsterdam'), ('Amsterdam', 'Split'),
    ('Amsterdam', 'Stockholm'), ('Stockholm', 'Amsterdam'),
    ('Amsterdam', 'Riga'), ('Riga', 'Amsterdam'),
    ('Vienna', 'Stockholm'), ('Stockholm', 'Vienna'),
    ('Vienna', 'Istanbul'), ('Istanbul', 'Vienna'),
    ('Vienna', 'Seville'), ('Seville', 'Vienna'),
    ('Istanbul', 'Amsterdam'), ('Amsterdam', 'Istanbul'),
    ('Munich', 'Brussels'), ('Brussels', 'Munich'),
    ('Prague', 'Munich'), ('Munich', 'Prague'),
    ('Riga', 'Munich'), ('Munich', 'Riga'),
    ('Prague', 'Amsterdam'), ('Amsterdam', 'Prague'),
    ('Prague', 'Brussels'), ('Brussels', 'Prague'),
    ('Prague', 'Istanbul'), ('Istanbul', 'Prague'),
    ('Vienna', 'Prague'), ('Prague', 'Vienna'),
    ('Munich', 'Split'), ('Split', 'Munich'),
    ('Vienna', 'Amsterdam'), ('Amsterdam', 'Vienna'),
    ('Prague', 'Stockholm'), ('Stockholm', 'Prague'),
    ('Brussels', 'Seville'), ('Seville', 'Brussels'),
    ('Munich', 'Stockholm'), ('Stockholm', 'Munich'),
    ('Istanbul', 'Brussels'), ('Brussels', 'Istanbul'),
    ('Amsterdam', 'Seville'), ('Seville', 'Amsterdam'),
    ('Vienna', 'Split'), ('Split', 'Vienna'),
    ('Munich', 'Seville'), ('Seville', 'Munich'),
    ('Riga', 'Brussels'), ('Brussels', 'Riga'),
    ('Prague', 'Riga'), ('Riga', 'Prague'),
    ('Vienna', 'Munich'), ('Munich', 'Vienna')
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

# All stays must be within 1-20 days
for city in cities:
    s.add(start[city] >= 1)
    s.add(end[city] <= 20)

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
    print("No valid trip plan exists. Check if total required days exceed 20, fixed dates overlap, or flight connections are insufficient.")