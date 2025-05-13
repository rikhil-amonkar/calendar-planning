from z3 import *

# Define cities and their required durations
cities = {
    'Warsaw': 4,
    'Venice': 3,
    'Vilnius': 3,
    'Salzburg': 4,
    'Amsterdam': 2,
    'Barcelona': 5,
    'Paris': 2,
    'Hamburg': 4,
    'Florence': 5,
    'Tallinn': 2
}

# Fixed date constraints
fixed = {
    'Paris': (1, 2),
    'Barcelona': (2, 6),
    'Tallinn': (11, 12),
    'Hamburg': (19, 22),
    'Salzburg': (22, 25)
}

# Direct flight pairs (note unidirectional Tallinn→Vilnius)
flight_pairs = [
    ('Paris', 'Venice'), ('Venice', 'Paris'),
    ('Barcelona', 'Amsterdam'), ('Amsterdam', 'Barcelona'),
    ('Amsterdam', 'Warsaw'), ('Warsaw', 'Amsterdam'),
    ('Amsterdam', 'Vilnius'), ('Vilnius', 'Amsterdam'),
    ('Barcelona', 'Warsaw'), ('Warsaw', 'Barcelona'),
    ('Warsaw', 'Venice'), ('Venice', 'Warsaw'),
    ('Amsterdam', 'Hamburg'), ('Hamburg', 'Amsterdam'),
    ('Barcelona', 'Hamburg'), ('Hamburg', 'Barcelona'),
    ('Barcelona', 'Florence'), ('Florence', 'Barcelona'),
    ('Barcelona', 'Venice'), ('Venice', 'Barcelona'),
    ('Paris', 'Hamburg'), ('Hamburg', 'Paris'),
    ('Paris', 'Vilnius'), ('Vilnius', 'Paris'),
    ('Paris', 'Amsterdam'), ('Amsterdam', 'Paris'),
    ('Paris', 'Florence'), ('Florence', 'Paris'),
    ('Florence', 'Amsterdam'), ('Amsterdam', 'Florence'),
    ('Vilnius', 'Warsaw'), ('Warsaw', 'Vilnius'),
    ('Barcelona', 'Tallinn'), ('Tallinn', 'Barcelona'),
    ('Paris', 'Warsaw'), ('Warsaw', 'Paris'),
    ('Tallinn', 'Warsaw'), ('Warsaw', 'Tallinn'),
    ('Tallinn', 'Vilnius'),  # Unidirectional
    ('Amsterdam', 'Tallinn'), ('Tallinn', 'Amsterdam'),
    ('Paris', 'Tallinn'), ('Tallinn', 'Paris'),
    ('Paris', 'Barcelona'), ('Barcelona', 'Paris'),
    ('Venice', 'Hamburg'), ('Hamburg', 'Venice'),
    ('Warsaw', 'Hamburg'), ('Hamburg', 'Warsaw'),
    ('Hamburg', 'Salzburg'), ('Salzburg', 'Hamburg'),
    ('Amsterdam', 'Venice'), ('Venice', 'Amsterdam')
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
    print("No valid trip plan exists. Check if total required days exceed 25, fixed dates overlap, or flight connections are insufficient.")