import z3

# Define cities with their durations and fixed intervals
cities = {
    'Vienna': 4,
    'Lyon': 3,
    'Edinburgh': (5, 8),
    'Reykjavik': 5,
    'Stuttgart': 5,
    'Manchester': 2,
    'Split': (19, 23),
    'Prague': 4
}

# Direct flight pairs (undirected)
flight_pairs = [
    frozenset(['Reykjavik', 'Stuttgart']),
    frozenset(['Stuttgart', 'Split']),
    frozenset(['Stuttgart', 'Vienna']),
    frozenset(['Prague', 'Manchester']),
    frozenset(['Edinburgh', 'Prague']),
    frozenset(['Manchester', 'Split']),
    frozenset(['Prague', 'Vienna']),
    frozenset(['Vienna', 'Manchester']),
    frozenset(['Prague', 'Split']),
    frozenset(['Vienna', 'Lyon']),
    frozenset(['Stuttgart', 'Edinburgh']),
    frozenset(['Split', 'Lyon']),
    frozenset(['Stuttgart', 'Manchester']),
    frozenset(['Prague', 'Lyon']),
    frozenset(['Reykjavik', 'Vienna']),
    frozenset(['Prague', 'Reykjavik']),
    frozenset(['Vienna', 'Split'])
]

# Initialize solver
solver = z3.Solver()

# Create variables for non-fixed cities
city_vars = {}
non_fixed = ['Vienna', 'Lyon', 'Reykjavik', 'Stuttgart', 'Manchester', 'Prague']
for city in non_fixed:
    start = z3.Int(f'start_{city}')
    end = z3.Int(f'end_{city}')
    duration = cities[city]
    solver.add(end == start + duration - 1)
    solver.add(start >= 1, end <= 25)
    city_vars[city] = (start, end)

# Add fixed cities
fixed = {
    'Edinburgh': (5, 8),
    'Split': (19, 23)
}
for city, (s, e) in fixed.items():
    city_vars[city] = (z3.IntVal(s), z3.IntVal(e))

# Collect all cities
all_cities = list(cities.keys())

# Each city's start is 1 or matches another's end; end is 25 or matches another's start
for city in all_cities:
    start, end = city_vars[city]
    others = [c for c in all_cities if c != city]
    solver.add(z3.Or(start == 1, z3.Or([start == city_vars[other][1] for other in others])))
    solver.add(z3.Or(end == 25, z3.Or([end == city_vars[other][0] for other in others])))

# Flight constraints for consecutive cities
for a in all_cities:
    for b in all_cities:
        if a == b:
            continue
        a_end = city_vars[a][1]
        b_start = city_vars[b][0]
        solver.add(z3.Implies(a_end == b_start, frozenset([a, b]) in flight_pairs))

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