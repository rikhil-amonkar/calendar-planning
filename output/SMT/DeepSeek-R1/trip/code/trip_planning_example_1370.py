import z3

# Define cities with their durations and fixed intervals
cities = {
    'Santorini': (25, 29),
    'Krakow': (18, 22),
    'Paris': (11, 15),
    'Vilnius': 3,
    'Munich': 5,
    'Geneva': 2,
    'Amsterdam': 4,
    'Budapest': 5,
    'Split': 4,
}

# Direct flights as directed edges
flight_routes = [
    ('Paris', 'Krakow'),
    ('Krakow', 'Paris'),
    ('Paris', 'Amsterdam'),
    ('Amsterdam', 'Paris'),
    ('Paris', 'Split'),
    ('Split', 'Paris'),
    ('Vilnius', 'Munich'),
    ('Paris', 'Geneva'),
    ('Geneva', 'Paris'),
    ('Amsterdam', 'Geneva'),
    ('Geneva', 'Amsterdam'),
    ('Munich', 'Split'),
    ('Split', 'Munich'),
    ('Split', 'Krakow'),
    ('Krakow', 'Split'),
    ('Munich', 'Amsterdam'),
    ('Amsterdam', 'Munich'),
    ('Budapest', 'Amsterdam'),
    ('Amsterdam', 'Budapest'),
    ('Split', 'Geneva'),
    ('Geneva', 'Split'),
    ('Vilnius', 'Split'),
    ('Split', 'Vilnius'),
    ('Munich', 'Geneva'),
    ('Geneva', 'Munich'),
    ('Munich', 'Krakow'),
    ('Krakow', 'Munich'),
    ('Krakow', 'Vilnius'),
    ('Vilnius', 'Amsterdam'),
    ('Amsterdam', 'Vilnius'),
    ('Budapest', 'Paris'),
    ('Paris', 'Budapest'),
    ('Krakow', 'Amsterdam'),
    ('Amsterdam', 'Krakow'),
    ('Vilnius', 'Paris'),
    ('Paris', 'Vilnius'),
    ('Budapest', 'Geneva'),
    ('Geneva', 'Budapest'),
    ('Split', 'Amsterdam'),
    ('Amsterdam', 'Split'),
    ('Santorini', 'Geneva'),
    ('Geneva', 'Santorini'),
    ('Amsterdam', 'Santorini'),
    ('Santorini', 'Amsterdam'),
    ('Munich', 'Budapest'),
    ('Budapest', 'Munich'),
    ('Munich', 'Paris'),
    ('Paris', 'Munich'),
]

# Initialize solver
solver = z3.Solver()

# Create variables for non-fixed cities
city_vars = {}
non_fixed = ['Vilnius', 'Munich', 'Geneva', 'Amsterdam', 'Budapest', 'Split']
for city in non_fixed:
    start = z3.Int(f'start_{city}')
    end = z3.Int(f'end_{city}')
    duration = cities[city]
    solver.add(end == start + duration - 1)
    solver.add(start >= 1, end <= 30)
    city_vars[city] = (start, end)

# Add fixed cities
fixed = {
    'Santorini': (25, 29),
    'Krakow': (18, 22),
    'Paris': (11, 15)
}
for city, (s, e) in fixed.items():
    city_vars[city] = (z3.IntVal(s), z3.IntVal(e))

# Collect all cities
all_cities = list(cities.keys())

# Each city's start is 1 or matches another's end; end is 30 or matches another's start
for city in all_cities:
    start, end = city_vars[city]
    others = [c for c in all_cities if c != city]
    solver.add(z3.Or(start == 1, z3.Or([start == city_vars[other][1] for other in others])))
    solver.add(z3.Or(end == 30, z3.Or([end == city_vars[other][0] for other in others])))

# Flight constraints: if a's end == b's start, then (a, b) must be in flight_routes
for a in all_cities:
    for b in all_cities:
        if a == b:
            continue
        a_end = city_vars[a][1]
        b_start = city_vars[b][0]
        if (a, b) not in flight_routes:
            solver.add(a_end != b_start)

# Check and print solution
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