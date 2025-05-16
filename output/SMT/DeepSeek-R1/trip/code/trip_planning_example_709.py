from z3 import *

# Define cities and their required durations
cities = {
    'Helsinki': 4,
    'Valencia': 5,
    'Dubrovnik': 4,
    'Porto': 3,
    'Prague': 3,
    'Reykjavik': 4
}

# Define direct flights as frozenset pairs
direct_flights = {
    frozenset({'Helsinki', 'Prague'}),
    frozenset({'Prague', 'Valencia'}),
    frozenset({'Valencia', 'Porto'}),
    frozenset({'Helsinki', 'Reykjavik'}),
    frozenset({'Dubrovnik', 'Helsinki'}),
    frozenset({'Reykjavik', 'Prague'})
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

# Each city's end_day is start_day + duration -1
for city in cities:
    solver.add(end_day[city] == start_day[city] + cities[city] - 1)

# First city starts on day 1
solver.add(Or([And(position[city] == 1, start_day[city] == 1) for city in cities]))

# Last city ends on day 18
solver.add(Or([And(position[city] == 6, end_day[city] == 18) for city in cities]))

# Flight and transition constraints between consecutive cities
for c1 in cities:
    for c2 in cities:
        if c1 == c2:
            continue
        # Consecutive cities must have flight and aligned days
        flight = frozenset({c1, c2}) in direct_flights
        solver.add(Implies(position[c2] == position[c1] + 1, 
                          And(start_day[c2] == end_day[c1], flight)))

# Porto must start on day 16 (meeting constraint)
solver.add(start_day['Porto'] == 16)

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