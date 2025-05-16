from z3 import *

# Define cities and their required durations
cities = {
    'Frankfurt': 4,
    'Manchester': 4,
    'Valencia': 4,
    'Naples': 4,
    'Oslo': 3,
    'Vilnius': 2
}

# Direct flights represented as frozenset pairs
direct_flights = {
    frozenset({'Valencia', 'Frankfurt'}),
    frozenset({'Manchester', 'Frankfurt'}),
    frozenset({'Naples', 'Manchester'}),
    frozenset({'Naples', 'Frankfurt'}),
    frozenset({'Naples', 'Oslo'}),
    frozenset({'Oslo', 'Frankfurt'}),
    frozenset({'Vilnius', 'Frankfurt'}),
    frozenset({'Oslo', 'Vilnius'}),
    frozenset({'Manchester', 'Oslo'}),
    frozenset({'Valencia', 'Naples'})
}

solver = Solver()

# Create variables for each city: position, start_day, end_day
position = {city: Int(f'pos_{city}') for city in cities}
start_day = {city: Int(f'start_{city}') for city in cities}
end_day = {city: Int(f'end_{city}') for city in cities}

# All positions are distinct and between 1-6
solver.add(Distinct([position[city] for city in cities]))
for city in cities:
    solver.add(position[city] >= 1, position[city] <= 6)

# Fixed positions for Frankfurt, Vilnius, and Oslo
solver.add(position['Frankfurt'] == 6)
solver.add(position['Vilnius'] == 5)
solver.add(position['Oslo'] == 4)

# Fixed start and end days for Frankfurt, Vilnius, and Oslo
solver.add(start_day['Frankfurt'] == 13, end_day['Frankfurt'] == 16)
solver.add(start_day['Vilnius'] == 12, end_day['Vilnius'] == 13)
solver.add(start_day['Oslo'] == 10, end_day['Oslo'] == 12)

# Each city's end_day is start_day + duration -1
for city in cities:
    solver.add(end_day[city] == start_day[city] + cities[city] - 1)

# First city starts on day 1
solver.add(Or([And(position[city] == 1, start_day[city] == 1) for city in cities if city not in ['Frankfurt', 'Vilnius', 'Oslo']]))

# Consecutive cities must have direct flights and aligned days
for c1 in cities:
    for c2 in cities:
        if c1 == c2:
            continue
        # Consecutive cities must have a flight and aligned days
        flight = frozenset({c1, c2}) in direct_flights
        solver.add(Implies(position[c2] == position[c1] + 1, 
                          And(start_day[c2] == end_day[c1], flight)))

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