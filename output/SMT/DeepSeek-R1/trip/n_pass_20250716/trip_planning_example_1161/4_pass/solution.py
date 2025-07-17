from z3 import *

# Define cities and their durations
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

# Define directed flight connections
directed_flights = [
    ('Oslo', 'Krakow'),
    ('Oslo', 'Paris'),
    ('Paris', 'Madrid'),
    ('Helsinki', 'Vilnius'),
    ('Oslo', 'Madrid'),
    ('Oslo', 'Helsinki'),
    ('Helsinki', 'Krakow'),
    ('Dubrovnik', 'Helsinki'),
    ('Dubrovnik', 'Madrid'),
    ('Oslo', 'Dubrovnik'),
    ('Krakow', 'Paris'),
    ('Madrid', 'Mykonos'),
    ('Oslo', 'Vilnius'),
    ('Krakow', 'Vilnius'),
    ('Helsinki', 'Paris'),
    ('Vilnius', 'Paris'),
    ('Helsinki', 'Madrid'),
    ('Krakow', 'Oslo'),
    ('Paris', 'Oslo'),
    ('Madrid', 'Paris'),
    ('Vilnius', 'Helsinki'),
    ('Madrid', 'Oslo'),
    ('Helsinki', 'Oslo'),
    ('Krakow', 'Helsinki'),
    ('Helsinki', 'Dubrovnik'),
    ('Madrid', 'Dubrovnik'),
    ('Dubrovnik', 'Oslo'),
    ('Paris', 'Krakow'),
    ('Mykonos', 'Madrid'),
    ('Vilnius', 'Oslo'),
    ('Vilnius', 'Krakow'),
    ('Paris', 'Helsinki'),
    ('Paris', 'Vilnius'),
    ('Madrid', 'Helsinki')
]

# Create Z3 variables for start and end days
start_vars = {city: Int(f'start_{city}') for city in cities}
end_vars = {city: Int(f'end_{city}') for city in cities}

solver = Solver()

# Fixed start days
solver.add(start_vars['Mykonos'] == 15)
solver.add(start_vars['Dubrovnik'] == 2)

# Duration constraints: end = start + duration - 1
for city in cities:
    solver.add(end_vars[city] == start_vars[city] + durations[city] - 1)
    solver.add(start_vars[city] >= 1)
    solver.add(end_vars[city] <= 18)

# Oslo must include day 1 or 2
solver.add(Or(
    And(start_vars['Oslo'] <= 1, end_vars['Oslo'] >= 1),
    And(start_vars['Oslo'] <= 2, end_vars['Oslo'] >= 2)
))

# Ensure all intervals are disjoint and cover [1,18]
days = range(1, 19)
for i in days:
    in_city = []
    for city in cities:
        in_city.append(And(start_vars[city] <= i, i <= end_vars[city]))
    solver.add(Or(in_city))  # At least one city covers the day
    
    # At most one city covers the day
    for j in range(len(cities)):
        for k in range(j+1, len(cities)):
            c1 = cities[j]
            c2 = cities[k]
            solver.add(Not(And(in_city[j], in_city[k])))

# Flight connectivity: consecutive cities must have direct flights
for c1 in cities:
    for c2 in cities:
        if c1 != c2:
            next_day = end_vars[c1] + 1
            condition = And(next_day <= 18, start_vars[c2] == next_day)
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