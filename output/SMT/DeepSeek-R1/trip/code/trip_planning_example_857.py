from z3 import *

# Define cities and their required days
cities = {
    'Porto': 2,
    'Geneva': 3,
    'Mykonos': 3,
    'Manchester': 4,
    'Hamburg': 5,
    'Naples': 5,
    'Frankfurt': 2
}

# Direct flights (note unidirectional Hamburg to Geneva)
direct_flights = [
    ('Hamburg', 'Frankfurt'),
    ('Frankfurt', 'Hamburg'),
    ('Naples', 'Mykonos'),
    ('Mykonos', 'Naples'),
    ('Hamburg', 'Porto'),
    ('Porto', 'Hamburg'),
    ('Hamburg', 'Geneva'),  # Unidirectional
    ('Mykonos', 'Geneva'),
    ('Geneva', 'Mykonos'),
    ('Frankfurt', 'Geneva'),
    ('Geneva', 'Frankfurt'),
    ('Frankfurt', 'Porto'),
    ('Porto', 'Frankfurt'),
    ('Geneva', 'Porto'),
    ('Porto', 'Geneva'),
    ('Geneva', 'Manchester'),
    ('Manchester', 'Geneva'),
    ('Naples', 'Manchester'),
    ('Manchester', 'Naples'),
    ('Frankfurt', 'Naples'),
    ('Naples', 'Frankfurt'),
    ('Frankfurt', 'Manchester'),
    ('Manchester', 'Frankfurt'),
    ('Naples', 'Geneva'),
    ('Geneva', 'Naples'),
    ('Porto', 'Manchester'),
    ('Manchester', 'Porto'),
    ('Hamburg', 'Manchester'),
    ('Manchester', 'Hamburg')
]

# Correct city name typos and ensure flights are tuples
corrected_flights = []
for a, b in direct_flights:
    a = a.strip().title()
    b = b.strip().title()
    a = 'Hamburg' if a == 'Hamburg' else a
    corrected_flights.append((a, b))
direct_flights = list(set([tuple(sorted([a, b])) if a < b else (a, b) for a, b in corrected_flights]))

s = Solver()

# Create start and end day variables for each city
start = {city: Int(f'start_{city}') for city in cities}
end = {city: Int(f'end_{city}') for city in cities}

# Fixed constraints
s.add(start['Frankfurt'] == 5, end['Frankfurt'] == 6)  # Days 5-6
s.add(start['Mykonos'] == 10, end['Mykonos'] == 12)     # Days 10-12
s.add(start['Manchester'] == 15, end['Manchester'] == 18) # Days 15-18

# Duration constraints for other cities
for city in cities:
    if city not in ['Frankfurt', 'Mykonos', 'Manchester']:
        s.add(end[city] - start[city] + 1 == cities[city])
        s.add(start[city] >= 1, end[city] <= 18)

# Ensure at least one non-fixed city starts on day 1
non_fixed = ['Porto', 'Geneva', 'Hamburg', 'Naples']
s.add(Or([start[city] == 1 for city in non_fixed]))

# Predecessor constraints for all cities
for city in cities:
    predecessors = []
    for other in cities:
        if other == city:
            continue
        # Check if flight exists from 'other' to 'city'
        flight_exists = Or(*[And(a == other, b == city) for a, b in direct_flights])
        predecessors.append(And(end[other] == start[city], flight_exists))
    if city in ['Frankfurt', 'Mykonos', 'Manchester']:
        s.add(Or(predecessors))  # Fixed start cities require predecessor
    else:
        s.add(Implies(start[city] > 1, Or(predecessors)))  # Others only if start >1

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