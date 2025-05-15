import z3

# Define cities with their durations and fixed intervals
cities = {
    'Naples': (1, 5),
    'Vienna': 7,
    'Vilnius': 7,
}

flight_routes = [
    ('Naples', 'Vienna'),
    ('Vienna', 'Vilnius'),
]

solver = z3.Solver()

# Create variables for non-fixed cities
city_vars = {}
fixed_cities = ['Naples']
for city in cities:
    if city in fixed_cities:
        s, e = cities[city]
        city_vars[city] = (z3.IntVal(s), z3.IntVal(e))
    else:
        duration = cities[city]
        start = z3.Int(f'start_{city}')
        end = z3.Int(f'end_{city}')
        solver.add(end == start + duration - 1)
        solver.add(start >= 1, end <= 17)
        city_vars[city] = (start, end)

# Total days constraint accounting for overlaps
total_days = sum((end - start + 1) for (start, end) in city_vars.values())

# Calculate overlaps between connected cities
overlap_pairs = []
for a, b in flight_routes:
    a_s, a_e = city_vars[a]
    b_s, b_e = city_vars[b]
    overlap = z3.If(z3.And(a_s <= b_e, b_s <= a_e),
                    z3.Min(a_e, b_e) - z3.Max(a_s, b_s) + 1,
                    0)
    overlap_pairs.append(overlap)

solver.add(total_days - sum(overlap_pairs) == 17)

# Cities without direct flights must not overlap or be consecutive
all_cities = list(cities.keys())
flight_pairs = set()
for a, b in flight_routes:
    flight_pairs.add((a, b))
    flight_pairs.add((b, a))

for a in all_cities:
    for b in all_cities:
        if a == b or (a, b) in flight_pairs:
            continue
        a_s, a_e = city_vars[a]
        b_s, b_e = city_vars[b]
        solver.add(z3.Or(b_e < a_s, a_e + 1 < b_s))

# Find and print solution
if solver.check() == z3.sat:
    model = solver.model()
    schedule = []
    for city in all_cities:
        s = model.evaluate(city_vars[city][0])
        e = model.evaluate(city_vars[city][1])
        s_val = s.as_long() if isinstance(s, z3.IntNumRef) else cities[city][0]
        e_val = e.as_long() if isinstance(e, z3.IntNumRef) else cities[city][1]
        schedule.append((city, s_val, e_val))
    schedule.sort(key=lambda x: x[1])
    print("Valid itinerary:")
    for entry in schedule:
        print(f"{entry[0]}: Days {entry[1]} to {entry[2]}")
else:
    print("No valid itinerary found.")