from z3 import *

# Define cities and their required durations
cities = {
    'Venice': 3,
    'Reykjavik': 2,
    'Munich': 3,
    'Santorini': 3,
    'Manchester': 3,
    'Porto': 3,
    'Bucharest': 5,
    'Tallinn': 4,
    'Valencia': 2,
    'Vienna': 5
}

# Fixed date constraints
fixed = {
    'Munich': (4, 6),
    'Santorini': (8, 10),
    'Valencia': (14, 15)
}

# Direct flight pairs (bidirectional)
flight_pairs = [
    ('Bucharest', 'Manchester'), ('Manchester', 'Bucharest'),
    ('Munich', 'Venice'), ('Venice', 'Munich'),
    ('Santorini', 'Manchester'), ('Manchester', 'Santorini'),
    ('Vienna', 'Reykjavik'), ('Reykjavik', 'Vienna'),
    ('Venice', 'Santorini'), ('Santorini', 'Venice'),
    ('Munich', 'Porto'), ('Porto', 'Munich'),
    ('Valencia', 'Vienna'), ('Vienna', 'Valencia'),
    ('Manchester', 'Vienna'), ('Vienna', 'Manchester'),
    ('Porto', 'Vienna'), ('Vienna', 'Porto'),
    ('Venice', 'Manchester'), ('Manchester', 'Venice'),
    ('Santorini', 'Vienna'), ('Vienna', 'Santorini'),
    ('Munich', 'Manchester'), ('Manchester', 'Munich'),
    ('Munich', 'Reykjavik'), ('Reykjavik', 'Munich'),
    ('Bucharest', 'Valencia'), ('Valencia', 'Bucharest'),
    ('Venice', 'Vienna'), ('Vienna', 'Venice'),
    ('Bucharest', 'Vienna'), ('Vienna', 'Bucharest'),
    ('Porto', 'Manchester'), ('Manchester', 'Porto'),
    ('Munich', 'Vienna'), ('Vienna', 'Munich'),
    ('Valencia', 'Porto'), ('Porto', 'Valencia'),
    ('Munich', 'Bucharest'), ('Bucharest', 'Munich'),
    ('Tallinn', 'Munich'), ('Munich', 'Tallinn'),
    ('Santorini', 'Bucharest'), ('Bucharest', 'Santorini'),
    ('Munich', 'Valencia'), ('Valencia', 'Munich')
]

# Build direct_flights dictionary (one-directional)
direct_flights = {city: [] for city in cities}
for a, b in flight_pairs:
    a_fixed = a.capitalize()  # Normalize city name casing
    b_fixed = b.capitalize()
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

# All stays must be within 1-24 days
for city in cities:
    s.add(start[city] >= 1)
    s.add(end[city] <= 24)

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
    print("No valid trip plan exists. Check if total required days exceed 24, fixed dates overlap, or flight connections are insufficient.")