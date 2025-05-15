from z3 import *

# Define cities and their required days
cities = {
    'Bucharest': 4,
    'Munich': 5,
    'Seville': 5,
    'Milan': 2,
    'Stockholm': 5,
    'Tallinn': 2
}

# Direct flights (including bidirectional)
direct_flights = [
    ('Milan', 'Stockholm'),
    ('Stockholm', 'Milan'),
    ('Munich', 'Stockholm'),
    ('Stockholm', 'Munich'),
    ('Bucharest', 'Munich'),
    ('Munich', 'Bucharest'),
    ('Munich', 'Seville'),
    ('Seville', 'Munich'),
    ('Stockholm', 'Tallinn'),
    ('Tallinn', 'Stockholm'),
    ('Munich', 'Milan'),
    ('Milan', 'Munich'),
    ('Munich', 'Tallinn'),
    ('Tallinn', 'Munich'),
    ('Seville', 'Milan'),
    ('Milan', 'Seville'),
]

s = Solver()

# Create start and end day variables for each city
start = {city: Int(f'start_{city}') for city in cities}
end = {city: Int(f'end_{city}') for city in cities}

# Fixed constraints
s.add(start['Bucharest'] == 1, end['Bucharest'] == 4)    # Days 1-4
s.add(start['Munich'] == 4, end['Munich'] == 8)          # Days 4-8
s.add(start['Seville'] == 8, end['Seville'] == 12)       # Days 8-12

# Duration constraints for other cities
s.add(end['Milan'] - start['Milan'] + 1 == 2)
s.add(end['Stockholm'] - start['Stockholm'] + 1 == 5)
s.add(end['Tallinn'] - start['Tallinn'] + 1 == 2)

# All days must be within 1-18
for city in ['Milan', 'Stockholm', 'Tallinn']:
    s.add(start[city] >= 1, end[city] <= 18)

# Predecessor constraints for all cities except Bucharest
for city in cities:
    if city == 'Bucharest':
        continue
    predecessors = []
    for other in cities:
        if other == city:
            continue
        # Check if flight exists between 'other' and 'city'
        flight_exists = Or(*[And(a == other, b == city) for a, b in direct_flights])
        predecessors.append(And(end[other] == start[city], flight_exists))
    s.add(Or(predecessors))

# Ensure the total trip ends by day 18
s.add(Or([end[city] == 18 for city in cities]))

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