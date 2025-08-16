from z3 import Solver, Int, If, And, Or, Distinct, sat
import json

# There are 6 cities with the following fixed durations:
# 0: Tallinn (2 days)
# 1: Bucharest (4 days) -- must include a day between 1 and 4 (visit relatives)
# 2: Seville (5 days)  -- must include a day between 8 and 12 (meet friends)
# 3: Stockholm (5 days)
# 4: Munich (5 days)   -- must include a day between 4 and 8 (attend wedding)
# 5: Milan (2 days)
cities = ["Tallinn", "Bucharest", "Seville", "Stockholm", "Munich", "Milan"]
durations = [2, 4, 5, 5, 5, 2]

# Allowed direct flights between cities (bidirectional).
# Each tuple (u,v) means that a direct flight exists between city u and city v.
allowed_pairs = [
    (5, 3), (3, 5),   # Milan and Stockholm
    (4, 3), (3, 4),   # Munich and Stockholm
    (1, 4), (4, 1),   # Bucharest and Munich
    (4, 2), (2, 4),   # Munich and Seville
    (3, 0), (0, 3),   # Stockholm and Tallinn
    (4, 5), (5, 4),   # Munich and Milan
    (4, 0), (0, 4),   # Munich and Tallinn
    (2, 5), (5, 2)    # Seville and Milan
]

# The overall trip is 18 days, but note that when switching cities on a flight day,
# that day counts for both cities. (For example, if you leave A on day X and arrive to B 
# on day X, then A is counted for [start_day_A, X] and B for [X, end_day_B].)
# The durations add up to 23 days; subtracting 5 flight overlap days gives 18.

# We model the itinerary as a permutation of the 6 cities.
# For the city in position p:
#   Let T[p] be the start day for that city.
#   The city’s stay lasts [T[p], T[p] + duration - 1].
# The flight between the cities in consecutive positions happens on the day T[p+1] (which is also the last day of city at position p).
# So the chaining constraints are:
#   T[0] = 1
#   For p = 0 .. 4: T[p+1] = T[p] + (duration of city at position p) - 1
#   And for the last city (at position 5): T[5] + (duration of city at position 5) - 1 = 18

# Create the solver
solver = Solver()

n = 6
# order[p] is the index of the city at itinerary position p.
order = [Int(f"order_{p}") for p in range(n)]
for p in range(n):
    solver.add(Or([order[p] == i for i in range(n)]))
solver.add(Distinct(order))

# T[p] is the start day for the city at position p.
T = [Int(f"T_{p}") for p in range(n)]
for p in range(n):
    # start days are at least 1
    solver.add(T[p] >= 1)

# Set the first city to start on Day 1.
solver.add(T[0] == 1)

# For each position p, determine the duration of the city assigned there.
def duration_at(p):
    return (
        If(order[p] == 0, durations[0],
        If(order[p] == 1, durations[1],
        If(order[p] == 2, durations[2],
        If(order[p] == 3, durations[3],
        If(order[p] == 4, durations[4],
           durations[5])))))
       
# Chain the start times together.
for p in range(n - 1):
    # The flight happens on the day T[p+1], which is also the last day of city at position p.
    # So: T[p+1] = T[p] + (duration of city at position p) - 1.
    solver.add(T[p+1] == T[p] + duration_at(p) - 1)

# The end day of the last city must be day 18.
solver.add(T[n-1] + duration_at(n-1) - 1 == 18)

# Flight connectivity constraint: For each consecutive pair in the itinerary,
# a direct flight must exist between them.
for p in range(n - 1):
    # city at position p is order[p] and next city is order[p+1]
    # Add constraint that (order[p], order[p+1]) is in allowed_pairs.
    flight_allowed = []
    for (u, v) in allowed_pairs:
        flight_allowed.append(And(order[p] == u, order[p+1] == v))
    solver.add(Or(flight_allowed))

# Add event-specific constraints.
# Bucharest (city index 1) must be visited early: its interval [T, T+3] must intersect [1,4].
# Intersection means: start <= 4 and (start + 4 - 1) >= 1. (The second is automatic since start>=1.)
for p in range(n):
    solver.add(If(order[p] == 1, T[p] <= 4, True))

# Munich (city index 4) must include the wedding between day 4 and day 8.
# Its interval [T, T+4] must intersect [4,8]: so T <= 8.
for p in range(n):
    solver.add(If(order[p] == 4, T[p] <= 8, True))

# Seville (city index 2) must include the friends meeting between day 8 and day 12.
# Its interval [T, T+4] must intersect [8,12]: 
# That is T <= 12 and T + 5 - 1 (i.e. T+4) >= 8  =>  T >= 4.
for p in range(n):
    solver.add(If(order[p] == 2, And(T[p] <= 12, T[p] >= 4), True))

# Solve the constraints.
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    # Build the itinerary segments in the order positions 0..5.
    for p in range(n):
        city_index = model.evaluate(order[p]).as_long()
        city_name = cities[city_index]
        start_day = model.evaluate(T[p]).as_long()
        # End day for this city is start_day + (duration) - 1.
        end_day = start_day + durations[city_index] - 1
        itinerary.append({
            "city": city_name,
            "start_day": start_day,
            "end_day": end_day
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=4))
else:
    print("No solution found.")