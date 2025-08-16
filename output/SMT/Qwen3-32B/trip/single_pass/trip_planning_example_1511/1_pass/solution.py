import z3
import json

# Define cities and their durations
cities_list = ['Venice', 'Reykjavik', 'Munich', 'Santorini', 'Manchester', 'Porto', 'Bucharest', 'Tallinn', 'Valencia', 'Vienna']
direct_flights = {
    ('Bucharest', 'Manchester'),
    ('Munich', 'Venice'),
    ('Santorini', 'Manchester'),
    ('Vienna', 'Reykjavik'),
    ('Venice', 'Santorini'),
    ('Munich', 'Porto'),
    ('Valencia', 'Vienna'),
    ('Manchester', 'Vienna'),
    ('Porto', 'Vienna'),
    ('Venice', 'Manchester'),
    ('Santorini', 'Vienna'),
    ('Munich', 'Manchester'),
    ('Munich', 'Reykjavik'),
    ('Bucharest', 'Valencia'),
    ('Venice', 'Vienna'),
    ('Bucharest', 'Vienna'),
    ('Porto', 'Manchester'),
    ('Munich', 'Vienna'),
    ('Valencia', 'Porto'),
    ('Munich', 'Bucharest'),
    ('Tallinn', 'Munich'),
    ('Santorini', 'Bucharest'),
    ('Munich', 'Valencia'),
}

# Create EnumSort for cities
City, cities_consts = z3.EnumSort('City', cities_list)

durations = {
    'Venice': 3,
    'Reykjavik': 2,
    'Munich': 3,
    'Santorini': 3,
    'Manchester': 3,
    'Porto': 3,
    'Bucharest': 5,
    'Tallinn': 4,
    'Valencia': 2,
    'Vienna': 5
}

# Map each city constant to its duration
duration_func = z3.Function('duration_func', City, z3.IntSort())
s = z3.Solver()

# Add duration constraints
for i, city_name in enumerate(cities_list):
    s.add(duration_func(cities_consts[i]) == durations[city_name])

# Create variables for the sequence of cities
positions = [z3.Const(f'pos_{i}', City) for i in range(10)]
s.add(z3.Distinct(positions))

# Create S0 variable and enforce start on day 1
S0 = z3.Int('S0')
s.add(S0 == 1)

# Create start_days for each position
start_days = [z3.Int(f'start_day_{i}') for i in range(10)]

# Add constraints for start_days
s.add(start_days[0] == S0)
for i in range(1, 10):
    s.add(start_days[i] == start_days[i-1] + duration_func(positions[i-1]) - 1)

# Add constraints for fixed start_days
# For Munich: start_day == 4
# For Santorini: start_day == 8
# For Valencia: start_day == 14
for m in range(10):
    s.add(z3.Implies(positions[m] == cities_consts[2], start_days[m] == 4))  # Munich is cities_consts[2]
for m in range(10):
    s.add(z3.Implies(positions[m] == cities_consts[3], start_days[m] == 8))  # Santorini is cities_consts[3]
for m in range(10):
    s.add(z3.Implies(positions[m] == cities_consts[8], start_days[m] == 14))  # Valencia is cities_consts[8]

# Add constraints for direct flights between consecutive cities
allowed_pairs = list(direct_flights)
for i in range(9):
    current_city = positions[i]
    next_city = positions[i+1]
    constraints = []
    for (city1_name, city2_name) in allowed_pairs:
        # Find the corresponding city constants
        city1 = None
        city2 = None
        for c in cities_consts:
            if c.name() == city1_name:
                city1 = c
            if c.name() == city2_name:
                city2 = c
        if city1 and city2:
            constraints.append(z3.And(current_city == city1, next_city == city2))
    s.add(z3.Or(constraints))

# Check if the solver can find a solution
if s.check() == z3.sat:
    model = s.model()
    # Extract the sequence of cities
    sequence = [model.eval(p) for p in positions]
    # Extract start_days values
    start_days_values = [model.eval(sd).as_long() for sd in start_days]
    # Generate the itinerary
    itinerary = {}
    for i in range(10):
        city = sequence[i]
        city_name = city.name()
        start = start_days_values[i]
        duration = durations[city_name]
        end = start + duration - 1
        for day in range(start, end + 1):
            itinerary[day] = city_name
    # Ensure all days from 1 to 24 are covered
    sorted_days = sorted(itinerary.keys())
    assert sorted_days == list(range(1, 25)), "Days not covered properly"
    # Output as JSON
    print(json.dumps({'itinerary': [{'day': day, 'city': city} for day, city in sorted(itinerary.items())]}))
else:
    print("No solution found")