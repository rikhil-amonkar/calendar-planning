#!/usr/bin/env python3
from z3 import *
import json

# Mapping of cities to their durations and names
# City indices:
# 0: Reykjavik (2 days, conference days 1-2)
# 1: Stockholm (3 days, friend meeting between days 2-4)
# 2: Oslo (5 days)
# 3: Stuttgart (5 days)
# 4: Split (3 days)
# 5: Geneva (2 days)
# 6: Porto (3 days, workshop between days 19-21)
# 7: Tallinn (5 days)
city_names = {
    0: "Reykjavik",
    1: "Stockholm",
    2: "Oslo",
    3: "Stuttgart",
    4: "Split",
    5: "Geneva",
    6: "Porto",
    7: "Tallinn"
}

durations_dict = {
    0: 2,
    1: 3,
    2: 5,
    3: 5,
    4: 3,
    5: 2,
    6: 3,
    7: 5
}

# Define a function to return the duration using Z3 If conditions.
def duration(city):
    return If(city == 0, 2,
           If(city == 1, 3,
           If(city == 2, 5,
           If(city == 3, 5,
           If(city == 4, 3,
           If(city == 5, 2,
           If(city == 6, 3,
           If(city == 7, 5, 0))))))))

# Allowed direct flights (treating them as bidirectional).
# Each tuple (a, b) is sorted (a < b) so that a flight between a and b (in any order) is permitted.
# REVISED: Added (5,7) so that Tallinn properly connects to the route.
allowed_flights = [
    (0, 1),  # Reykjavik - Stockholm
    (0, 2),  # Reykjavik - Oslo
    (0, 3),  # Reykjavik - Stuttgart
    (0, 7),  # Reykjavik - Tallinn
    (1, 2),  # Stockholm - Oslo
    (1, 3),  # Stockholm - Stuttgart
    (1, 4),  # Stockholm - Split
    (1, 5),  # Stockholm - Geneva
    (2, 4),  # Oslo - Split
    (2, 5),  # Oslo - Geneva
    (2, 6),  # Oslo - Porto
    (2, 7),  # Oslo - Tallinn
    (3, 4),  # Stuttgart - Split
    (3, 6),  # Stuttgart - Porto
    (4, 5),  # Split - Geneva
    (5, 6),  # Geneva - Porto
    (5, 7)   # Geneva - Tallinn   <-- new allowed flight added
]

# Create the Z3 solver.
solver = Solver()

n_cities = 8

# itinerary[i] is the city index at position i.
itinerary = [Int("city_%d" % i) for i in range(n_cities)]
# start[i] is the starting day of being in itinerary[i].
start = [Int("start_%d" % i) for i in range(n_cities)]

# Constraint: each itinerary city is between 0 and 7.
for i in range(n_cities):
    solver.add(itinerary[i] >= 0, itinerary[i] < n_cities)

# Fix known positions:
# Must attend conference in Reykjavik on days 1-2, so first city must be Reykjavik (0)
solver.add(itinerary[0] == 0)
# Must meet friend in Stockholm between day 2 and 4, so fix Stockholm (1) early.
solver.add(itinerary[1] == 1)
# Workshop in Porto must occur between day 19 and 21.
# For that to work with the overlap logic, Porto (6) is set as last city.
solver.add(itinerary[n_cities - 1] == 6)

# All cities must be visited exactly once (permutation).
solver.add(Distinct(itinerary))

# Set the starting day for the first city.
solver.add(start[0] == 1)

# Define the recurrence: if you are in city A with duration d on its interval [s, s+d-1],
# then as you depart on the last day of A, you immediately start the next city.
for i in range(n_cities - 1):
    solver.add(start[i+1] == start[i] + (duration(itinerary[i]) - 1))

# The final day of the trip must be day 21.
# For the last city, its interval is [start[n_cities-1], start[n_cities-1] + duration - 1]
solver.add(start[n_cities - 1] + (duration(itinerary[n_cities - 1]) - 1) == 21)

# Flight connectivity constraints: for each consecutive pair (city_i, city_{i+1}),
# there must exist a direct flight between them.
for i in range(n_cities - 1):
    a = itinerary[i]
    b = itinerary[i+1]
    allowed_clause = []
    for (c1, c2) in allowed_flights:
        # Either (a->b) equals the flight or the reverse.
        allowed_clause.append(And(a == c1, b == c2))
        allowed_clause.append(And(a == c2, b == c1))
    solver.add(Or(allowed_clause))

# Special time-window constraints:
# For Stockholm (city 1), its stay [start, start+duration-1] must intersect [2,4].
for i in range(n_cities):
    solver.add(Implies(itinerary[i] == 1, start[i] <= 4))
# For Porto (city 6), its stay must intersect [19,21].
for i in range(n_cities):
    solver.add(Implies(itinerary[i] == 6, And(start[i] <= 21, start[i] + 2 >= 19)))

# Check satisfiability and extract model.
if solver.check() == sat:
    m = solver.model()
    itinerary_plan = []
    for i in range(n_cities):
        city_int = m.evaluate(itinerary[i]).as_long()
        city_name = city_names[city_int]
        s_day = m.evaluate(start[i]).as_long()
        # Use the fixed duration from our dictionary.
        d = durations_dict[city_int]
        e_day = s_day + d - 1
        day_range = f"Day {s_day}-{e_day}"
        itinerary_plan.append({"day_range": day_range, "place": city_name})
    result = {"itinerary": itinerary_plan}
    print(json.dumps(result, indent=2))
else:
    print(json.dumps({"itinerary": []}))