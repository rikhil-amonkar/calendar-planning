import z3

# Define cities with their durations and fixed dates where applicable
cities = {
    'Athens': (6, (1, 6)),
    'Naples': (5, (16, 20)),
    'Valencia': 6,
    'Zurich': 6,
}

# Define flight connections as a set of tuples
flight_pairs = {
    ('Valencia', 'Naples'),
    ('Valencia', 'Athens'),
    ('Athens', 'Naples'),
    ('Zurich', 'Naples'),
    ('Athens', 'Zurich'),
    ('Zurich', 'Valencia'),
}

# Helper function to check if two cities are connected
def is_connected(a, b):
    return (a, b) in flight_pairs or (b, a) in flight_pairs

# Initialize solver
solver = z3.Solver()

# Create variables for Valencia and Zurich
valencia_start = z3.Int('valencia_start')
valencia_end = z3.Int('valencia_end')
zurich_start = z3.Int('zurich_start')
zurich_end = z3.Int('zurich_end')

# Duration constraints
solver.add(valencia_end == valencia_start + 6 - 1)
solver.add(zurich_end == zurich_start + 6 - 1)

# Cities must be within 1-20 days
solver.add(valencia_start >= 1, valencia_end <= 20)
solver.add(zurich_start >= 1, zurich_end <= 20)

# Define the two possible valid sequences
case1 = z3.And(
    zurich_start == 6,
    zurich_end == 11,
    valencia_start == 11,
    valencia_end == 16,
    z3.BoolVal(is_connected('Athens', 'Zurich')),
    z3.BoolVal(is_connected('Zurich', 'Valencia')),
    z3.BoolVal(is_connected('Valencia', 'Naples'))
)

case2 = z3.And(
    valencia_start == 6,
    valencia_end == 11,
    zurich_start == 11,
    zurich_end == 16,
    z3.BoolVal(is_connected('Athens', 'Valencia')),
    z3.BoolVal(is_connected('Valencia', 'Zurich')),
    z3.BoolVal(is_connected('Zurich', 'Naples'))
)

solver.add(z3.Or(case1, case2))

# Check solution and print
if solver.check() == z3.sat:
    model = solver.model()
    schedule = []
    for city in cities:
        if city in ['Athens', 'Naples']:
            start, end = cities[city][1]
        else:
            start = model[globals()[f"{city.lower()}_start"]].as_long()
            end = model[globals()[f"{city.lower()}_end"]].as_long()
        schedule.append((city, start, end))
    schedule.sort(key=lambda x: x[1])
    for entry in schedule:
        print(f"{entry[0]}: Days {entry[1]} to {entry[2]}")
else:
    print("No valid itinerary found.")