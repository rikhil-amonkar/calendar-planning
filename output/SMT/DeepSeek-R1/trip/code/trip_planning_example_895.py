from z3 import *

# Define cities and their required durations
cities = {
    'Brussels': 2,
    'Venice': 3,
    'Madrid': 5,
    'London': 3,
    'Lisbon': 4,
    'Reykjavik': 3,
    'Santorini': 3
}

# Directed flights represented as (from, to) tuples
directed_flights = {
    ('Venice', 'Madrid'), ('Madrid', 'Venice'),
    ('Lisbon', 'Reykjavik'), ('Reykjavik', 'Lisbon'),
    ('Brussels', 'Venice'), ('Venice', 'Brussels'),
    ('Venice', 'Santorini'), ('Santorini', 'Venice'),
    ('Lisbon', 'Venice'), ('Venice', 'Lisbon'),
    ('Reykjavik', 'Madrid'),
    ('Brussels', 'London'), ('London', 'Brussels'),
    ('Madrid', 'London'), ('London', 'Madrid'),
    ('Santorini', 'London'), ('London', 'Santorini'),
    ('London', 'Reykjavik'), ('Reykjavik', 'London'),
    ('Brussels', 'Lisbon'), ('Lisbon', 'Brussels'),
    ('Lisbon', 'London'), ('London', 'Lisbon'),
    ('Lisbon', 'Madrid'), ('Madrid', 'Lisbon'),
    ('Madrid', 'Santorini'), ('Santorini', 'Madrid'),
    ('Brussels', 'Reykjavik'), ('Reykjavik', 'Brussels'),
    ('Brussels', 'Madrid'), ('Madrid', 'Brussels'),
    ('Venice', 'London'), ('London', 'Venice')
}

solver = Solver()

# Create variables for each city: position, start_day, end_day
position = {city: Int(f'pos_{city}') for city in cities}
start_day = {city: Int(f'start_{city}') for city in cities}
end_day = {city: Int(f'end_{city}') for city in cities}

# Fixed constraints for Brussels, Venice, and Madrid
solver.add(position['Brussels'] == 1)
solver.add(start_day['Brussels'] == 1, end_day['Brussels'] == 2)
solver.add(start_day['Venice'] == 5, end_day['Venice'] == 7)
solver.add(start_day['Madrid'] == 7, end_day['Madrid'] == 11)

# All positions are distinct and between 1-7
solver.add(Distinct([position[city] for city in cities]))
for city in cities:
    solver.add(position[city] >= 1, position[city] <= 7)

# Duration constraints for all cities
for city in cities:
    solver.add(end_day[city] == start_day[city] + cities[city] - 1)

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