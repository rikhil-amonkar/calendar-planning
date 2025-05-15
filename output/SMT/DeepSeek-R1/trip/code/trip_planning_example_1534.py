from z3 import *

# Define cities and their required days
cities = {
    'Paris': 2,
    'Barcelona': 5,
    'Amsterdam': 2,
    'Warsaw': 4,
    'Venice': 3,
    'Vilnius': 3,
    'Hamburg': 4,
    'Salzburg': 4,
    'Florence': 5,
    'Tallinn': 2
}

# Direct flights (including bidirectional where applicable)
direct_flights = [
    ('Paris', 'Venice'),
    ('Venice', 'Paris'),
    ('Barcelona', 'Amsterdam'),
    ('Amsterdam', 'Barcelona'),
    ('Amsterdam', 'Warsaw'),
    ('Warsaw', 'Amsterdam'),
    ('Amsterdam', 'Vilnius'),
    ('Vilnius', 'Amsterdam'),
    ('Barcelona', 'Warsaw'),
    ('Warsaw', 'Barcelona'),
    ('Warsaw', 'Venice'),
    ('Venice', 'Warsaw'),
    ('Amsterdam', 'Hamburg'),
    ('Hamburg', 'Amsterdam'),
    ('Barcelona', 'Hamburg'),
    ('Hamburg', 'Barcelona'),
    ('Barcelona', 'Florence'),
    ('Florence', 'Barcelona'),
    ('Barcelona', 'Venice'),
    ('Venice', 'Barcelona'),
    ('Paris', 'Hamburg'),
    ('Hamburg', 'Paris'),
    ('Paris', 'Vilnius'),
    ('Vilnius', 'Paris'),
    ('Paris', 'Amsterdam'),
    ('Amsterdam', 'Paris'),
    ('Paris', 'Florence'),
    ('Florence', 'Paris'),
    ('Florence', 'Amsterdam'),
    ('Amsterdam', 'Florence'),
    ('Vilnius', 'Warsaw'),
    ('Warsaw', 'Vilnius'),
    ('Barcelona', 'Tallinn'),
    ('Tallinn', 'Barcelona'),
    ('Paris', 'Warsaw'),
    ('Warsaw', 'Paris'),
    ('Tallinn', 'Warsaw'),
    ('Warsaw', 'Tallinn'),
    ('Tallinn', 'Vilnius'),  # One-way
    ('Amsterdam', 'Tallinn'),
    ('Tallinn', 'Amsterdam'),
    ('Paris', 'Tallinn'),
    ('Tallinn', 'Paris'),
    ('Paris', 'Barcelona'),
    ('Barcelona', 'Paris'),
    ('Venice', 'Hamburg'),
    ('Hamburg', 'Venice'),
    ('Warsaw', 'Hamburg'),
    ('Hamburg', 'Warsaw'),
    ('Hamburg', 'Salzburg'),
    ('Salzburg', 'Hamburg'),
    ('Amsterdam', 'Venice'),
    ('Venice', 'Amsterdam')
]

s = Solver()

# Create start and end day variables for each city
start = {city: Int(f'start_{city}') for city in cities}
end = {city: Int(f'end_{city}') for city in cities}

# Fixed constraints
s.add(start['Paris'] == 1, end['Paris'] == 2)          # Paris: Days 1-2
s.add(start['Barcelona'] == 2, end['Barcelona'] == 6)   # Barcelona: Days 2-6
s.add(start['Tallinn'] == 11, end['Tallinn'] == 12)     # Tallinn: Days 11-12
s.add(start['Hamburg'] == 19, end['Hamburg'] == 22)     # Hamburg: Days 19-22
s.add(start['Salzburg'] == 22, end['Salzburg'] == 25)   # Salzburg: Days 22-25

# Duration constraints for other cities
s.add(end['Amsterdam'] - start['Amsterdam'] + 1 == 2)
s.add(end['Warsaw'] - start['Warsaw'] + 1 == 4)
s.add(end['Venice'] - start['Venice'] + 1 == 3)
s.add(end['Vilnius'] - start['Vilnius'] + 1 == 3)
s.add(end['Florence'] - start['Florence'] + 1 == 5)

# All days must be within 1-25
for city in ['Amsterdam', 'Warsaw', 'Venice', 'Vilnius', 'Florence']:
    s.add(start[city] >= 1, end[city] <= 25)

# Predecessor constraints for all cities except Paris
for city in cities:
    if city in ['Paris']:
        continue  # No predecessor for Paris
    predecessors = []
    for other in cities:
        if other == city:
            continue
        # Check if flight exists from 'other' to 'city'
        flight_exists = Or(*[And(a == other, b == city) for a, b in direct_flights])
        predecessors.append(And(end[other] == start[city], flight_exists))
    # For fixed cities, enforce predecessor explicitly
    if city in ['Barcelona', 'Tallinn', 'Hamburg', 'Salzburg']:
        s.add(Or(predecessors))
    else:
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