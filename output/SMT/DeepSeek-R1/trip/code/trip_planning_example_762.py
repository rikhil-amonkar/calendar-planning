import z3

# Define cities with their durations and fixed intervals
cities = {
    'Dublin': (7, 9),
    'Madrid': (2, 3),
    'Berlin': (3, 7),
    'Oslo': 3,
    'London': 2,
    'Vilnius': 3,
}

# Direct flights as bidirectional edges
flight_routes = [
    ('London', 'Madrid'),
    ('Oslo', 'Vilnius'),
    ('Berlin', 'Vilnius'),
    ('Madrid', 'Oslo'),
    ('Madrid', 'Dublin'),
    ('London', 'Oslo'),
    ('Madrid', 'Berlin'),
    ('Berlin', 'Oslo'),
    ('Dublin', 'Oslo'),
    ('London', 'Dublin'),
    ('London', 'Berlin'),
    ('Berlin', 'Dublin'),
]

solver = z3.Solver()

# Create variables for non-fixed cities
city_vars = {}
non_fixed = ['Oslo', 'London', 'Vilnius']
for city in non_fixed:
    start = z3.Int(f'start_{city}')
    end = z3.Int(f'end_{city}')
    duration = cities[city]
    solver.add(end == start + duration - 1)
    solver.add(start >= 1, end <= 13)
    city_vars[city] = (start, end)

# Add fixed cities
fixed = {
    'Dublin': (7, 9),
    'Madrid': (2, 3),
    'Berlin': (3, 7),
}
for city, (s, e) in fixed.items():
    city_vars[city] = (z3.IntVal(s), z3.IntVal(e))

# Collect all cities
all_cities = list(cities.keys())

# Ensure continuity between cities
for city in all_cities:
    start, end = city_vars[city]
    others = [c for c in all_cities if c != city]
    # Start of a city must be 1 or follow the end of another city with a flight
    solver.add(z3.Or(start == 1, z3.Or([end_other == start for other in others for end_other in [city_vars[other][1]])))
    # End of a city must be 13 or precede the start of another city with a flight
    solver.add(z3.Or(end == 13, z3.Or([start_other == end for other in others for start_other in [city_vars[other][0]]))))

# Flight constraints: consecutive cities must have a direct flight
for i in range(len(all_cities)):
    for j in range(len(all_cities)):
        if i == j:
            continue
        city_a = all_cities[i]
        city_b = all_cities[j]
        a_end = city_vars[city_a][1]
        b_start = city_vars[city_b][0]
        # If city_b starts right after city_a ends, there must be a flight
        solver.add(z3.Implies(b_start == a_end + 1, z3.Or([(city_a == route[0] and city_b == route[1]) for route in flight_routes)))

# Total days constraint
total_days = sum((city_vars[city][1] - city_vars[city][0] + 1) for city in all_cities)
solver.add(total_days == 13)

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