from z3 import *
import json

# Cities indexing
# 0: Lisbon, 1: Dubrovnik, 2: Copenhagen, 3: Prague,
# 4: Tallinn, 5: Stockholm, 6: Split, 7: Lyon
cities = ["Lisbon", "Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Stockholm", "Split", "Lyon"]
durations = [2, 5, 5, 3, 2, 4, 3, 2]  # required days in each city

# Allowed direct flights (bidirectional)
allowed_flights = [
    (1, 5),        # Dubrovnik - Stockholm
    (0, 2),        # Lisbon - Copenhagen
    (0, 7),        # Lisbon - Lyon
    (2, 5),        # Copenhagen - Stockholm
    (2, 6),        # Copenhagen - Split
    (3, 5),        # Prague - Stockholm
    (4, 5),        # Tallinn - Stockholm
    (3, 7),        # Prague - Lyon
    (0, 5),        # Lisbon - Stockholm
    (3, 0),        # Prague - Lisbon
    (5, 6),        # Stockholm - Split
    (3, 2),        # Prague - Copenhagen
    (6, 7),        # Split - Lyon
    (2, 1),        # Copenhagen - Dubrovnik
    (3, 6),        # Prague - Split
    (4, 2),        # Tallinn - Copenhagen
    (4, 3)         # Tallinn - Prague
]
# Add symmetric edges (if not already present)
symmetric_edges = [(b, a) for (a, b) in allowed_flights]
for edge in symmetric_edges:
    if edge not in allowed_flights:
        allowed_flights.append(edge)

# Number of cities in the itinerary
n = len(cities)

# Create SMT solver
solver = Solver()

# Create order variables: order[0] ... order[n-1], each is an integer in 0..n-1.
order = [Int(f"order_{i}") for i in range(n)]
for o in order:
    solver.add(o >= 0, o < n)
solver.add(Distinct(order))

# Create start day variables for each segment in the itinerary.
# The segment in position i will span from start[i] to end[i] = start[i] + duration - 1.
starts = [Int(f"start_{i}") for i in range(n)]

# For each itinerary segment, determine its duration based on the city chosen.
def duration_expr(i):
    # Sum of If conditions to pick the right duration from durations list.
    return Sum([If(order[i] == c, durations[c], 0) for c in range(n)])

# Chain timeline constraints:
# The trip starts on Day 1.
solver.add(starts[0] == 1)
for i in range(1, n):
    # The next segment begins on the same day the previous segment ends.
    # End day for segment i-1 is: starts[i-1] + duration_expr(i-1) - 1.
    solver.add(starts[i] == starts[i-1] + duration_expr(i-1) - 1)
# The trip must finish on Day 19.
solver.add(starts[n-1] + duration_expr(n-1) - 1 == 19)

# Flight connectivity constraint:
# For every consecutive pair in the itinerary, there must be a direct flight.
for i in range(n - 1):
    # Build a list of allowed connection conditions for the consecutive cities.
    conn_conditions = []
    for (a, b) in allowed_flights:
        conn_conditions.append(And(order[i] == a, order[i+1] == b))
    solver.add(Or(conn_conditions))

# Event constraints:
# Workshop in Lisbon (city 0) must be between day 4 and day 5.
for i in range(n):
    # If the city at position i is Lisbon then ensure its itinerary covers day 4 or day 5.
    # Its segment goes from starts[i] to starts[i] + duration_expr(i) - 1.
    workshop_cond = Or(
        And(starts[i] <= 4, 4 <= starts[i] + duration_expr(i) - 1),
        And(starts[i] <= 5, 5 <= starts[i] + duration_expr(i) - 1)
    )
    solver.add(Implies(order[i] == 0, workshop_cond))

# Meet a friend in Tallinn (city 4) between day 1 and day 2.
for i in range(n):
    friend_cond = Or(
        And(starts[i] <= 1, 1 <= starts[i] + duration_expr(i) - 1),
        And(starts[i] <= 2, 2 <= starts[i] + duration_expr(i) - 1)
    )
    solver.add(Implies(order[i] == 4, friend_cond))

# Wedding in Stockholm (city 5) must be between day 13 and day 16.
for i in range(n):
    wedding_cond = Or(
        And(starts[i] <= 13, 13 <= starts[i] + duration_expr(i) - 1),
        And(starts[i] <= 14, 14 <= starts[i] + duration_expr(i) - 1),
        And(starts[i] <= 15, 15 <= starts[i] + duration_expr(i) - 1),
        And(starts[i] <= 16, 16 <= starts[i] + duration_expr(i) - 1)
    )
    solver.add(Implies(order[i] == 5, wedding_cond))

# Annual show in Lyon (city 7) from day 18 to day 19.
for i in range(n):
    show_cond = Or(
        And(starts[i] <= 18, 18 <= starts[i] + duration_expr(i) - 1),
        And(starts[i] <= 19, 19 <= starts[i] + duration_expr(i) - 1)
    )
    solver.add(Implies(order[i] == 7, show_cond))

# Solve the SMT problem.
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(n):
        # Determine which city is at itinerary position i.
        city_index = model[order[i]].as_long()
        city_name = cities[city_index]
        seg_start = model[starts[i]].as_long()
        seg_duration = model.evaluate(duration_expr(i)).as_long()
        seg_end = seg_start + seg_duration - 1
        itinerary.append({
            "day_range": f"Day {seg_start}-{seg_end}",
            "place": city_name
        })
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print(json.dumps({"itinerary": []}))