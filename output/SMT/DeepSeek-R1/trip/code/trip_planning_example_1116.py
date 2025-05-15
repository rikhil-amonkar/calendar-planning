import z3

# Define cities with their durations and fixed intervals
cities = {
    'Oslo': (16, 17),
    'Reykjavik': (9, 13),
    'Munich': (13, 16),
    'Frankfurt': (17, 20),
    'Stockholm': 4,
    'Barcelona': 3,
    'Bucharest': 2,
    'Split': 3,
}

# Direct flights as directed edges
flight_routes = [
    ('Reykjavik', 'Munich'),
    ('Munich', 'Frankfurt'),
    ('Split', 'Oslo'),
    ('Reykjavik', 'Oslo'),
    ('Bucharest', 'Munich'),
    ('Oslo', 'Frankfurt'),
    ('Bucharest', 'Barcelona'),
    ('Barcelona', 'Frankfurt'),
    ('Reykjavik', 'Frankfurt'),
    ('Barcelona', 'Stockholm'),
    ('Barcelona', 'Reykjavik'),
    ('Stockholm', 'Reykjavik'),
    ('Barcelona', 'Split'),
    ('Bucharest', 'Oslo'),
    ('Bucharest', 'Frankfurt'),
    ('Split', 'Stockholm'),
    ('Barcelona', 'Oslo'),
    ('Stockholm', 'Munich'),
    ('Stockholm', 'Oslo'),
    ('Split', 'Frankfurt'),
    ('Barcelona', 'Munich'),
    ('Stockholm', 'Frankfurt'),
    ('Munich', 'Oslo'),
    ('Split', 'Munich'),
]

solver = z3.Solver()

# Create variables for non-fixed cities
city_vars = {}
non_fixed = ['Stockholm', 'Barcelona', 'Bucharest', 'Split']
for city in non_fixed:
    start = z3.Int(f'start_{city}')
    end = z3.Int(f'end_{city}')
    duration = cities[city]
    solver.add(end == start + duration - 1)
    solver.add(start >= 1, end <= 20)
    city_vars[city] = (start, end)

# Add fixed cities
fixed = {
    'Oslo': (16, 17),
    'Reykjavik': (9, 13),
    'Munich': (13, 16),
    'Frankfurt': (17, 20),
}
for city, (s, e) in fixed.items():
    city_vars[city] = (z3.IntVal(s), z3.IntVal(e))

# Collect all cities
all_cities = list(cities.keys())

# Ensure continuity between cities
for city in all_cities:
    start, end = city_vars[city]
    others = [c for c in all_cities if c != city]
    solver.add(z3.Or(start == 1, z3.Or([start == city_vars[other][1] for other in others])))
    solver.add(z3.Or(end == 20, z3.Or([end == city_vars[other][0] for other in others])))

# Flight constraints
flight_pairs = set(flight_routes)
for a in all_cities:
    for b in all_cities:
        if a == b:
            continue
        if (a, b) not in flight_pairs:
            a_end = city_vars[a][1]
            b_start = city_vars[b][0]
            solver.add(a_end != b_start)

# Total days constraint
total_days = sum((city_vars[city][1] - city_vars[city][0] + 1) for city in all_cities)
solver.add(total_days == 20)

# Check solution
if solver.check() == z3.sat:
    model = solver.model()
    schedule = []
    for city in all_cities:
        s = model[city_vars[city][0]]
        e = model[city_vars[city][1]]
        s_val = s.as_long() if isinstance(s, z3.IntNumRef) else city_vars[city][0].as_long()
        e_val = e.as_long() if isinstance(e, z3.IntNumRef) else city_vars[city][1].as_long()
        schedule.append((city, s_val, e_val))
    schedule.sort(key=lambda x: x[1])
    print("Valid itinerary:")
    for entry in schedule:
        print(f"{entry[0]}: Days {entry[1]} to {entry[2]}")
else:
    print("No valid itinerary found.")