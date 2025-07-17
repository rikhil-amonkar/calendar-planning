from z3 import *

# Define the cities and their durations
cities = ['Mykonos', 'Krakow', 'Vilnius', 'Helsinki', 'Dubrovnik', 'Oslo', 'Madrid', 'Paris']
durations = {
    'Mykonos': 4,
    'Krakow': 5,
    'Vilnius': 2,
    'Helsinki': 2,
    'Dubrovnik': 3,
    'Oslo': 2,
    'Madrid': 5,
    'Paris': 2
}

# Directed flights: (from, to) pairs
directed_flights = [
    ('Oslo', 'Krakow'),
    ('Krakow', 'Oslo'),
    ('Oslo', 'Paris'),
    ('Paris', 'Oslo'),
    ('Paris', 'Madrid'),
    ('Madrid', 'Paris'),
    ('Helsinki', 'Vilnius'),
    ('Vilnius', 'Helsinki'),
    ('Oslo', 'Madrid'),
    ('Madrid', 'Oslo'),
    ('Oslo', 'Helsinki'),
    ('Helsinki', 'Oslo'),
    ('Helsinki', 'Krakow'),
    ('Krakow', 'Helsinki'),
    ('Dubrovnik', 'Helsinki'),
    ('Helsinki', 'Dubrovnik'),
    ('Dubrovnik', 'Madrid'),
    ('Madrid', 'Dubrovnik'),
    ('Oslo', 'Dubrovnik'),
    ('Dubrovnik', 'Oslo'),
    ('Krakow', 'Paris'),
    ('Paris', 'Krakow'),
    ('Madrid', 'Mykonos'),
    ('Mykonos', 'Madrid'),
    ('Oslo', 'Vilnius'),
    ('Vilnius', 'Oslo'),
    ('Krakow', 'Vilnius'),
    ('Helsinki', 'Paris'),
    ('Paris', 'Helsinki'),
    ('Vilnius', 'Paris'),
    ('Paris', 'Vilnius'),
    ('Helsinki', 'Madrid'),
    ('Madrid', 'Helsinki')
]

# Create Z3 variables for start and end days
start_vars = {city: Int(f'start_{city}') for city in cities}
end_vars = {city: Int(f'end_{city}') for city in cities}

solver = Solver()

# Fixed start days
solver.add(start_vars['Mykonos'] == 15)
solver.add(start_vars['Dubrovnik'] == 3)

# Duration constraints: end = start + duration - 1
for city in cities:
    solver.add(end_vars[city] == start_vars[city] + durations[city] - 1)
    solver.add(start_vars[city] >= 1)
    solver.add(end_vars[city] <= 25)

# Oslo must start on day 1 or 2
solver.add(Or(start_vars['Oslo'] == 1, start_vars['Oslo'] == 2))

# Ensure all intervals are disjoint and cover [1,25]
for i in range(1, 26):  # each day from 1 to 25
    in_city = []
    for city in cities:
        in_city.append(And(start_vars[city] <= i, i <= end_vars[city]))
    solver.add(Or(in_city))  # at least one city covers the day

    # At most one city covers the day
    for idx1 in range(len(cities)):
        for idx2 in range(idx1 + 1, len(cities)):
            c1 = cities[idx1]
            c2 = cities[idx2]
            solver.add(Not(And(
                start_vars[c1] <= i, i <= end_vars[c1],
                start_vars[c2] <= i, i <= end_vars[c2]
            )))

# Flight connectivity: for any two cities, if one ends and the next starts the next day, require a flight
for c1 in cities:
    for c2 in cities:
        if c1 != c2:
            next_start = end_vars[c1] + 1
            condition = And(next_start <= 25, start_vars[c2] == next_start)
            flight_required = Implies(condition, (c1, c2) in directed_flights)
            solver.add(flight_required)

# Check and get the model
if solver.check() == sat:
    model = solver.model()
    start_vals = {city: model.eval(start_vars[city]).as_long() for city in cities}
    end_vals = {city: model.eval(end_vars[city]).as_long() for city in cities}
    
    # Print the schedule
    schedule = sorted(cities, key=lambda city: start_vals[city])
    print("Trip Plan:")
    for city in schedule:
        print(f"{city}: from day {start_vals[city]} to day {end_vals[city]}")
    
    # Print the flight path
    print("\nFlight Path:")
    sorted_cities = sorted(cities, key=lambda city: start_vals[city])
    for i in range(len(sorted_cities) - 1):
        from_city = sorted_cities[i]
        to_city = sorted_cities[i+1]
        print(f"From {from_city} to {to_city} (day {end_vals[from_city] + 1})")
else:
    print("No solution found")