from z3 import *

# Define cities and their required durations
cities = {
    'Madrid': 4,
    'Dublin': 3,
    'Tallinn': 2
}

# Define direct flights as frozenset pairs
direct_flights = {
    frozenset({'Madrid', 'Dublin'}),
    frozenset({'Dublin', 'Tallinn'})
}

solver = Solver()

# Create variables for each city: position, start_day, end_day
position = {city: Int(f'pos_{city}') for city in cities}
start_day = {city: Int(f'start_{city}') for city in cities}
end_day = {city: Int(f'end_{city}') for city in cities}

# All positions are distinct and between 1-3
solver.add(Distinct([position[city] for city in cities]))
for city in cities:
    solver.add(position[city] >= 1, position[city] <= 3)

# Tallinn must be the last city (position 3) with fixed days 6-7
solver.add(position['Tallinn'] == 3)
solver.add(start_day['Tallinn'] == 6)
solver.add(end_day['Tallinn'] == 7)

# Duration constraints for all cities
for city in cities:
    solver.add(end_day[city] == start_day[city] + cities[city] - 1)

# First city starts on day 1
solver.add(Or([And(position[city] == 1, start_day[city] == 1) for city in cities]))

# Flight and transition constraints between consecutive cities
for c1 in cities:
    for c2 in cities:
        if c1 == c2:
            continue
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