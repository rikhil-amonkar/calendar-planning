from z3 import *

# Define cities and their required durations
cities = {
    'Vienna': 4,
    'Milan': 2,
    'Rome': 3,
    'Riga': 2,
    'Lisbon': 3,
    'Vilnius': 4,
    'Oslo': 3
}

# Directed flights represented as (from, to) tuples
directed_flights = {
    ('Riga', 'Oslo'), ('Oslo', 'Riga'),
    ('Rome', 'Oslo'), ('Oslo', 'Rome'),
    ('Vienna', 'Milan'), ('Milan', 'Vienna'),
    ('Vienna', 'Vilnius'), ('Vilnius', 'Vienna'),
    ('Vienna', 'Lisbon'), ('Lisbon', 'Vienna'),
    ('Riga', 'Milan'), ('Milan', 'Riga'),
    ('Lisbon', 'Oslo'), ('Oslo', 'Lisbon'),
    ('Rome', 'Riga'), ('Rome', 'Lisbon'), ('Lisbon', 'Rome'),
    ('Vienna', 'Riga'), ('Riga', 'Vienna'),
    ('Vienna', 'Rome'), ('Rome', 'Vienna'),
    ('Milan', 'Oslo'), ('Oslo', 'Milan'),
    ('Vienna', 'Oslo'), ('Oslo', 'Vienna'),
    ('Vilnius', 'Oslo'), ('Oslo', 'Vilnius'),
    ('Riga', 'Vilnius'), ('Vilnius', 'Milan'), ('Milan', 'Vilnius'),
    ('Riga', 'Lisbon'), ('Lisbon', 'Riga'),
    ('Milan', 'Lisbon'), ('Lisbon', 'Milan')
}

solver = Solver()

# Create variables for each city: position, start_day, end_day
position = {city: Int(f'pos_{city}') for city in cities}
start_day = {city: Int(f'start_{city}') for city in cities}
end_day = {city: Int(f'end_{city}') for city in cities}

# All positions are distinct and between 1-7
solver.add(Distinct([position[city] for city in cities]))
for city in cities:
    solver.add(position[city] >= 1, position[city] <= 7)

# Fixed constraints for Vienna, Lisbon, Oslo
solver.add(position['Vienna'] == 1)
solver.add(start_day['Vienna'] == 1, end_day['Vienna'] == 4)
solver.add(start_day['Lisbon'] == 11, end_day['Lisbon'] == 13)
solver.add(position['Oslo'] == 7, start_day['Oslo'] == 13, end_day['Oslo'] == 15)

# Duration constraints for all cities
for city in cities:
    solver.add(end_day[city] == start_day[city] + cities[city] - 1)

# Consecutive cities must have a direct flight and aligned days
for A in cities:
    for B in cities:
        if A == B:
            continue
        # Prevent invalid flights
        if (A, B) not in directed_flights:
            solver.add(Not(And(position[B] == position[A] + 1)))
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