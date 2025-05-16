from z3 import *

# Define cities and their required durations
cities = {
    'Porto': 3,
    'Vienna': 2,
    'Warsaw': 3,
    'Paris': 5,
    'Florence': 3,
    'Munich': 5,
    'Nice': 5
}

# Directed flights represented as (from, to) tuples
directed_flights = {
    ('Florence', 'Vienna'), ('Vienna', 'Florence'),
    ('Paris', 'Warsaw'), ('Warsaw', 'Paris'),
    ('Munich', 'Vienna'), ('Vienna', 'Munich'),
    ('Porto', 'Vienna'), ('Vienna', 'Porto'),
    ('Warsaw', 'Vienna'), ('Vienna', 'Warsaw'),
    ('Florence', 'Munich'),
    ('Munich', 'Warsaw'), ('Warsaw', 'Munich'),
    ('Munich', 'Nice'), ('Nice', 'Munich'),
    ('Paris', 'Florence'), ('Florence', 'Paris'),
    ('Warsaw', 'Nice'), ('Nice', 'Warsaw'),
    ('Porto', 'Munich'), ('Munich', 'Porto'),
    ('Porto', 'Nice'), ('Nice', 'Porto'),
    ('Paris', 'Vienna'), ('Vienna', 'Paris'),
    ('Nice', 'Vienna'), ('Vienna', 'Nice'),
    ('Porto', 'Paris'), ('Paris', 'Porto'),
    ('Paris', 'Nice'), ('Nice', 'Paris'),
    ('Paris', 'Munich'), ('Munich', 'Paris'),
    ('Porto', 'Warsaw'), ('Warsaw', 'Porto')
}

solver = Solver()

# Create variables for each city: position, start_day, end_day
position = {city: Int(f'pos_{city}') for city in cities}
start_day = {city: Int(f'start_{city}') for city in cities}
end_day = {city: Int(f'end_{city}') for city in cities}

# Fixed constraints for Porto, Vienna, Warsaw
solver.add(position['Porto'] == 1)
solver.add(start_day['Porto'] == 1, end_day['Porto'] == 3)
solver.add(start_day['Vienna'] == 19, end_day['Vienna'] == 20)
solver.add(start_day['Warsaw'] == 13, end_day['Warsaw'] == 15)

# All positions are distinct and between 1-7
solver.add(Distinct([position[city] for city in cities]))
for city in cities:
    solver.add(position[city] >= 1, position[city] <= 7)

# Duration constraints for all cities
for city in cities:
    solver.add(end_day[city] == start_day[city] + cities[city] - 1)
    solver.add(start_day[city] >= 1, end_day[city] <= 20)

# Flight and transition constraints between consecutive cities
for A in cities:
    for B in cities:
        if A == B:
            continue
        # Prevent invalid flights
        if (A, B) not in directed_flights:
            solver.add(Not(position[B] == position[A] + 1))
        # Align days for consecutive cities
        solver.add(Implies(position[B] == position[A] + 1,
                          start_day[B] == end_day[A]))

# Check for solution and output
if solver.check() == sat:
    model = solver.model()
    ordered = sorted(cities.keys(), key=lambda x: model.evaluate(position[x]).as_long())
    print("Valid Trip Plan:")
    for city in ordered:
        s = model.evaluate(start_day[city]).as_long()
        e = model.evaluate(end_day[city]).as_long()
        print(f"{city}: Days {s} to {e}")
else:
    print("No valid trip plan found.")