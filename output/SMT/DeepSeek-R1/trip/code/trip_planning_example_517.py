from z3 import *

# Define cities and their required days
cities = {
    'Bucharest': 6,
    'Stuttgart': 7,
    'Warsaw': 2,
    'Copenhagen': 3,
    'Dubrovnik': 5
}

# Direct flights (including bidirectional where applicable)
direct_flights = [
    ('Warsaw', 'Copenhagen'),
    ('Copenhagen', 'Warsaw'),
    ('Stuttgart', 'Copenhagen'),
    ('Copenhagen', 'Stuttgart'),
    ('Warsaw', 'Stuttgart'),
    ('Stuttgart', 'Warsaw'),
    ('Bucharest', 'Copenhagen'),
    ('Copenhagen', 'Bucharest'),
    ('Bucharest', 'Warsaw'),
    ('Warsaw', 'Bucharest'),
    ('Copenhagen', 'Dubrovnik'),
    ('Dubrovnik', 'Copenhagen'),
]

s = Solver()

# Create start and end day variables for each city
start = {city: Int(f'start_{city}') for city in cities}
end = {city: Int(f'end_{city}') for city in cities}

# Fixed constraints
s.add(start['Bucharest'] == 1, end['Bucharest'] == 6)     # Bucharest: Days 1-6
s.add(start['Stuttgart'] == 7, end['Stuttgart'] == 13)     # Stuttgart: Days 7-13

# Duration constraints for other cities
s.add(end['Warsaw'] - start['Warsaw'] + 1 == 2)
s.add(end['Copenhagen'] - start['Copenhagen'] + 1 == 3)
s.add(end['Dubrovnik'] - start['Dubrovnik'] + 1 == 5)

# All days must be within 1-19
for city in ['Warsaw', 'Copenhagen', 'Dubrovnik']:
    s.add(start[city] >= 1, end[city] <= 19)

# Predecessor constraints for all cities except Bucharest
for city in cities:
    if city == 'Bucharest':
        continue
    predecessors = []
    for other in cities:
        if other == city:
            continue
        # Check if flight exists from 'other' to 'city'
        flight_exists = Or(*[And(a == other, b == city) for a, b in direct_flights])
        predecessors.append(And(end[other] == start[city], flight_exists))
    s.add(Or(predecessors))

# Solve and output
if s.check() == sat:
    m = s.model()
    schedule = []
    for city in cities:
        s_day = m.eval(start[city]).as_long()
        e_day = m.eval(end[city]).as_long()
        schedule.append((s_day, e_day, city))
    schedule.sort()
    print("Travel Plan:")
    for s_day, e_day, city in schedule:
        print(f"{city}: Days {s_day} to {e_day}")
else:
    print("No valid schedule found")