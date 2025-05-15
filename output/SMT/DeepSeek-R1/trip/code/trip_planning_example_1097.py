import z3

# Define cities with their durations and fixed intervals
cities = {
    'Reykjavik': 4,
    'Riga': (2, (4, 5)),
    'Oslo': 3,
    'Lyon': 5,
    'Dubrovnik': (2, (7, 8)),
    'Madrid': 2,
    'Warsaw': 4,
    'London': 3
}

# Directed flight connections (from, to)
directed_flights = [
    ('Warsaw', 'Reykjavik'),
    ('Reykjavik', 'Warsaw'),
    ('Oslo', 'Madrid'),
    ('Madrid', 'Oslo'),
    ('Warsaw', 'Riga'),
    ('Riga', 'Warsaw'),
    ('Lyon', 'London'),
    ('London', 'Lyon'),
    ('Madrid', 'London'),
    ('London', 'Madrid'),
    ('Warsaw', 'London'),
    ('London', 'Warsaw'),
    ('Reykjavik', 'Madrid'),
    ('Warsaw', 'Oslo'),
    ('Oslo', 'Warsaw'),
    ('Oslo', 'Dubrovnik'),
    ('Dubrovnik', 'Oslo'),
    ('Oslo', 'Reykjavik'),
    ('Reykjavik', 'Oslo'),
    ('Riga', 'Oslo'),
    ('Oslo', 'Riga'),
    ('Oslo', 'Lyon'),
    ('Lyon', 'Oslo'),
    ('Oslo', 'London'),
    ('London', 'Oslo'),
    ('London', 'Reykjavik'),
    ('Reykjavik', 'London'),
    ('Warsaw', 'Madrid'),
    ('Madrid', 'Warsaw'),
    ('Madrid', 'Lyon'),
    ('Lyon', 'Madrid'),
    ('Dubrovnik', 'Madrid'),
    ('Madrid', 'Dubrovnik')
]

# Initialize solver
solver = z3.Solver()

# Create variables for non-fixed cities
non_fixed = ['Reykjavik', 'Oslo', 'Lyon', 'Madrid', 'Warsaw', 'London']
vars = {city: (z3.Int(f'{city.lower()}_start'), z3.Int(f'{city.lower()}_end')) for city in non_fixed}

# Duration constraints for non-fixed cities
solver.add(vars['Reykjavik'][1] == vars['Reykjavik'][0] + 4 - 1)
solver.add(vars['Oslo'][1] == vars['Oslo'][0] + 3 - 1)
solver.add(vars['Lyon'][1] == vars['Lyon'][0] + 5 - 1)
solver.add(vars['Madrid'][1] == vars['Madrid'][0] + 2 - 1)
solver.add(vars['Warsaw'][1] == vars['Warsaw'][0] + 4 - 1)
solver.add(vars['London'][1] == vars['London'][0] + 3 - 1)

# Fixed cities' intervals
riga_start, riga_end = 4, 5
dubrovnik_start, dubrovnik_end = 7, 8

# All intervals must be within 1-18
for city in non_fixed:
    solver.add(vars[city][0] >= 1, vars[city][1] <= 18)

# Collect all cities with their start/end variables
all_cities = [
    ('Reykjavik', vars['Reykjavik'][0], vars['Reykjavik'][1]),
    ('Riga', riga_start, riga_end),
    ('Oslo', vars['Oslo'][0], vars['Oslo'][1]),
    ('Lyon', vars['Lyon'][0], vars['Lyon'][1]),
    ('Dubrovnik', dubrovnik_start, dubrovnik_end),
    ('Madrid', vars['Madrid'][0], vars['Madrid'][1]),
    ('Warsaw', vars['Warsaw'][0], vars['Warsaw'][1]),
    ('London', vars['London'][0], vars['London'][1])
]

# Ensure trip starts on day 1 and ends on day 18
solver.add(z3.Or(*(var[0] == 1 for (name, var) in vars.items())))
solver.add(z3.Or(*(var[1] == 18 for (name, var) in vars.items())))

# Flight connection constraints between consecutive cities
for a in all_cities:
    a_name, a_start, a_end = a
    for b in all_cities:
        b_name, b_start, b_end = b
        if a_name == b_name:
            continue
        # Handle fixed/variable start/end
        a_end_expr = a_end if isinstance(a_end, z3.ExprRef) else a_end
        b_start_expr = b_start if isinstance(b_start, z3.ExprRef) else b_start
        solver.add(z3.Implies(a_end_expr == b_start_expr, z3.BoolVal((a_name, b_name) in directed_flights)))

# Check solution
if solver.check() == z3.sat:
    model = solver.model()
    schedule = []
    for city in all_cities:
        name, start, end = city
        if name in ['Riga', 'Dubrovnik']:
            s, e = start, end
        else:
            s = model[start].as_long()
            e = model[end].as_long()
        schedule.append((name, s, e))
    # Sort by start day
    schedule.sort(key=lambda x: x[1])
    print("Valid itinerary:")
    for entry in schedule:
        print(f"{entry[0]}: Days {entry[1]} to {entry[2]}")
else:
    print("No valid itinerary found.")