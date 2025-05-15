import z3

# Define cities with their durations and fixed intervals where applicable
cities = {
    'Hamburg': 7,
    'Munich': 6,
    'Manchester': (2, (19, 20)),
    'Lyon': (2, (13, 14)),
    'Split': 7
}

# Directed flight connections (from, to)
directed_flights = [
    ('Split', 'Munich'),
    ('Munich', 'Split'),
    ('Munich', 'Manchester'),
    ('Manchester', 'Munich'),
    ('Hamburg', 'Manchester'),
    ('Manchester', 'Hamburg'),
    ('Hamburg', 'Munich'),
    ('Munich', 'Hamburg'),
    ('Split', 'Lyon'),
    ('Lyon', 'Split'),
    ('Lyon', 'Munich'),
    ('Munich', 'Lyon'),
    ('Hamburg', 'Split'),
    ('Split', 'Hamburg'),
    ('Manchester', 'Split')
]

# Initialize solver
solver = z3.Solver()

# Create variables for non-fixed cities
hamburg_start = z3.Int('hamburg_start')
hamburg_end = z3.Int('hamburg_end')
munich_start = z3.Int('munich_start')
munich_end = z3.Int('munich_end')
split_start = z3.Int('split_start')
split_end = z3.Int('split_end')

# Duration constraints
solver.add(hamburg_end == hamburg_start + 7 - 1)
solver.add(munich_end == munich_start + 6 - 1)
solver.add(split_end == split_start + 7 - 1)

# Fixed cities' intervals
manchester_start, manchester_end = 19, 20
lyon_start, lyon_end = 13, 14

# All intervals must be within 1-20
solver.add(hamburg_start >= 1, hamburg_end <= 20)
solver.add(munich_start >= 1, munich_end <= 20)
solver.add(split_start >= 1, split_end <= 20)

# Collect all cities with their start/end variables
all_cities = [
    ('Hamburg', hamburg_start, hamburg_end),
    ('Munich', munich_start, munich_end),
    ('Split', split_start, split_end),
    ('Lyon', lyon_start, lyon_end),
    ('Manchester', manchester_start, manchester_end)
]

# Ensure trip starts on day 1 and ends on day 20
solver.add(z3.Or(
    hamburg_start == 1,
    munich_start == 1,
    split_start == 1,
    lyon_start == 1
))
solver.add(z3.Or(
    hamburg_end == 20,
    munich_end == 20,
    split_end == 20,
    lyon_end == 20,
    manchester_end == 20
))

# Flight connection constraints between consecutive cities
for i in range(len(all_cities)):
    city_a, a_start, a_end = all_cities[i]
    for j in range(len(all_cities)):
        if i == j:
            continue
        city_b, b_start, b_end = all_cities[j]
        # If city_a ends when city_b starts, enforce flight exists
        solver.add(z3.Implies(
            a_end == b_start,
            z3.BoolVal((city_a, city_b) in directed_flights)
        ))

# Special constraints for fixed cities
# Manchester must be preceded by a city ending on 19
solver.add(z3.Or(
    hamburg_end == 19,
    munich_end == 19,
    split_end == 19
))
# Lyon must be preceded by a city ending on 13
solver.add(z3.Or(
    hamburg_end == 13,
    munich_end == 13,
    split_end == 13
))
# Lyon must be followed by a city starting on 14
solver.add(z3.Or(
    munich_start == 14,
    split_start == 14,
    hamburg_start == 14
))

# Check solution
if solver.check() == z3.sat:
    model = solver.model()
    schedule = []
    for city, start, end in all_cities:
        if city in ['Manchester', 'Lyon']:
            s, e = start, end
        else:
            s = model[start].as_long()
            e = model[end].as_long()
        schedule.append((city, s, e))
    # Sort by start day
    schedule.sort(key=lambda x: x[1])
    print("Valid itinerary:")
    for entry in schedule:
        print(f"{entry[0]}: Days {entry[1]} to {entry[2]}")
else:
    print("No valid itinerary found.")