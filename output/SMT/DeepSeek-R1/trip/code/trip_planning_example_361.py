from z3 import *

# Define cities and their required days
cities = {
    'Paris': 6,
    'Madrid': 7,
    'Bucharest': 2,
    'Seville': 3
}

# Direct flights (bidirectional)
direct_flights = [
    ('Paris', 'Bucharest'),
    ('Bucharest', 'Paris'),
    ('Seville', 'Paris'),
    ('Paris', 'Seville'),
    ('Madrid', 'Bucharest'),
    ('Bucharest', 'Madrid'),
    ('Madrid', 'Paris'),
    ('Paris', 'Madrid'),
    ('Madrid', 'Seville'),
    ('Seville', 'Madrid')
]

s = Solver()

# Create start and end day variables for each city
start = {city: Int(f'start_{city}') for city in cities}
end = {city: Int(f'end_{city}') for city in cities}

# Fixed constraints
s.add(start['Madrid'] == 1, end['Madrid'] == 7)       # Madrid: Days 1-7
s.add(start['Bucharest'] == 14, end['Bucharest'] == 15) # Bucharest: Days 14-15

# Duration constraints for Paris and Seville
s.add(end['Paris'] - start['Paris'] + 1 == 6)
s.add(end['Seville'] - start['Seville'] + 1 == 3)

# All days must be within 1-15
for city in ['Paris', 'Seville']:
    s.add(start[city] >= 1, end[city] <= 15)

# Predecessor constraints for all cities (except Madrid)
for city in cities:
    if city == 'Madrid':
        continue  # Madrid is the starting point
    predecessors = []
    for other in cities:
        if other == city:
            continue
        # Check if flight exists from 'other' to 'city'
        flight_exists = Or(*[And(a == other, b == city) for a, b in direct_flights])
        predecessors.append(And(end[other] == start[city], flight_exists))
    if city == 'Bucharest':
        # Bucharest's start is fixed to 14, so predecessor must end on 14
        s.add(Or(predecessors))
    else:
        # Paris and Seville must have a predecessor if their start > 1
        s.add(If(start[city] > 1, Or(predecessors), True))

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