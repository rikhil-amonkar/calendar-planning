import z3

# Define cities with their durations and fixed intervals
cities = {
    'Nice': (1, 5),
    'Frankfurt': (19, 20),
    'Dublin': 7,
    'Lyon': 4,
    'Krakow': 6
}

# Direct flight pairs (undirected)
flight_pairs = [
    frozenset(['Nice', 'Dublin']),
    frozenset(['Dublin', 'Frankfurt']),
    frozenset(['Dublin', 'Krakow']),
    frozenset(['Krakow', 'Frankfurt']),
    frozenset(['Lyon', 'Frankfurt']),
    frozenset(['Nice', 'Frankfurt']),
    frozenset(['Lyon', 'Dublin']),
    frozenset(['Nice', 'Lyon'])
]

# Initialize solver
solver = z3.Solver()

# Create variables for start days of non-fixed cities
d_start = z3.Int('d_start')
d_end = d_start + 6  # Dublin duration 7 days (start + 6)
l_start = z3.Int('l_start')
l_end = l_start + 3  # Lyon duration 4 days (start + 3)
k_start = z3.Int('k_start')
k_end = k_start + 5  # Krakow duration 6 days (start + 5)

# Variables dictionary for easier access
vars = {
    'Dublin': (d_start, d_end),
    'Lyon': (l_start, l_end),
    'Krakow': (k_start, k_end)
}

# Constraints for start and end days
solver.add(z3.Or(d_start == 5, l_start == 5, k_start == 5))  # One starts at 5
solver.add(z3.Or(d_end == 19, l_end == 19, k_end == 19))     # One ends at 19

# Chain constraints for non-fixed cities
for city in ['Dublin', 'Lyon', 'Krakow']:
    start, end = vars[city]
    # If not starting at 5, start must match another's end
    solver.add(z3.Implies(start != 5, z3.Or(
        start == d_end, start == l_end, start == k_end
    )))
    # If not ending at 19, end must match another's start
    solver.add(z3.Implies(end != 19, z3.Or(
        end == d_start, end == l_start, end == k_start
    )))

# Flight constraints between consecutive cities
for a in vars:
    for b in vars:
        if a == b:
            continue
        a_end = vars[a][1]
        b_start = vars[b][0]
        has_flight = frozenset((a, b)) in flight_pairs
        solver.add(z3.Implies(a_end == b_start, has_flight))

# Flight from Nice to the first city
solver.add(z3.Or(
    z3.And(d_start == 5, frozenset(('Nice', 'Dublin')) in flight_pairs),
    z3.And(l_start == 5, frozenset(('Nice', 'Lyon')) in flight_pairs)
)

# Flight to Frankfurt from the last city
solver.add(z3.Or(
    z3.And(d_end == 19, frozenset(('Dublin', 'Frankfurt')) in flight_pairs),
    z3.And(l_end == 19, frozenset(('Lyon', 'Frankfurt')) in flight_pairs),
    z3.And(k_end == 19, frozenset(('Krakow', 'Frankfurt')) in flight_pairs)
)

# All cities must be scheduled (start >=1 and <=18)
solver.add(d_start >= 5, d_end <= 19)
solver.add(l_start >= 5, l_end <= 19)
solver.add(k_start >= 5, k_end <= 19)

# Check solution
if solver.check() == z3.sat:
    model = solver.model()
    schedule = []
    # Collect all cities' intervals
    for city in cities:
        if city in ['Nice', 'Frankfurt']:
            s, e = cities[city]
        else:
            s = model[vars[city][0]].as_long()
            e = model[vars[city][1]].as_long()
        schedule.append((city, s, e))
    # Sort by start day
    schedule.sort(key=lambda x: x[1])
    print("Valid itinerary:")
    for entry in schedule:
        print(f"{entry[0]}: Days {entry[1]} to {entry[2]}")
else:
    print("No valid itinerary found.")