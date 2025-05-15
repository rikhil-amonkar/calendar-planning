import z3

# Define cities with their durations and fixed intervals
cities = {
    'Manchester': (1, 3),
    'Venice': (3, 9),
    'Istanbul': 7,
    'Krakow': 6,
    'Lyon': 2,
}

flight_routes = [
    ('Manchester', 'Venice'),
    ('Manchester', 'Istanbul'),
    ('Venice', 'Istanbul'),
    ('Istanbul', 'Krakow'),
    ('Venice', 'Lyon'),
    ('Lyon', 'Istanbul'),
    ('Manchester', 'Krakow'),
]

solver = z3.Solver()

# Create variables for non-fixed cities
city_vars = {}
fixed_cities = ['Manchester', 'Venice']
for city in cities:
    if city in fixed_cities:
        s, e = cities[city]
        city_vars[city] = (z3.IntVal(s), z3.IntVal(e))
    else:
        duration = cities[city]
        start = z3.Int(f'start_{city}')
        end = z3.Int(f'end_{city}')
        solver.add(end == start + duration - 1)
        solver.add(start >= 1, end <= 21)
        city_vars[city] = (start, end)

# Total days constraint
total_days = sum((end - start + 1) for (start, end) in city_vars.values())
solver.add(total_days == 21)

# Flight constraints
flight_pairs = set()
for a, b in flight_routes:
    flight_pairs.add((a, b))
    flight_pairs.add((b, a))

all_cities = list(cities.keys())
for a in all_cities:
    for b in all_cities:
        if a == b:
            continue
        a_s, a_e = city_vars[a]
        b_s, b_e = city_vars[b]
        if (a, b) not in flight_pairs:
            # No flight between a and b: cannot overlap and cannot be consecutive
            solver.add(z3.Not(z3.And(a_s <= b_e, b_s <= a_e)))  # No overlap
            solver.add(z3.Not(z3.Or(b_s == a_e + 1, a_s == b_e + 1)))  # No consecutive

# Check solution
if solver.check() == z3.sat:
    model = solver.model()
    schedule = []
    for city in all_cities:
        s = model.evaluate(city_vars[city][0])
        e = model.evaluate(city_vars[city][1])
        s_val = s.as_long() if isinstance(s, z3.IntNumRef) else city_vars[city][0].as_long()
        e_val = e.as_long() if isinstance(e, z3.IntNumRef) else city_vars[city][1].as_long()
        schedule.append((city, s_val, e_val))
    schedule.sort(key=lambda x: x[1])
    print("Valid itinerary:")
    for entry in schedule:
        print(f"{entry[0]}: Days {entry[1]} to {entry[2]}")
else:
    print("No valid itinerary found.")