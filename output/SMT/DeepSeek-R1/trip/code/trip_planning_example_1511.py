import z3

# Define cities with their durations and fixed intervals
cities = {
    'Venice': 3,
    'Reykjavik': 2,
    'Munich': (4, 6),
    'Santorini': (8, 10),
    'Manchester': 3,
    'Porto': 3,
    'Bucharest': 5,
    'Tallinn': 4,
    'Valencia': (14, 15),
    'Vienna': 5,
}

flight_routes = [
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
]

solver = z3.Solver()

# Create variables for non-fixed cities
city_vars = {}
fixed_cities = ['Munich', 'Santorini', 'Valencia']
for city in cities:
    if city in fixed_cities:
        s, e = cities[city]
        city_vars[city] = (z3.IntVal(s), z3.IntVal(e))
    else:
        duration = cities[city]
        start = z3.Int(f'start_{city}')
        end = z3.Int(f'end_{city}')
        solver.add(end == start + duration - 1)
        solver.add(start >= 1, end <= 24)
        city_vars[city] = (start, end)

# Total days constraint
total_days = sum((end - start + 1) for (start, end) in city_vars.values())
solver.add(total_days == 24)

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
            solver.add(z3.Not(z3.Or(b_s == a_e, b_s == a_e + 1)))  # No consecutive

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