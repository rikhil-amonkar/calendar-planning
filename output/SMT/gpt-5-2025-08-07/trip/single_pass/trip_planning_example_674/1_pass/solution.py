from z3 import *
import json

# Cities and indices
cities = ["Helsinki", "Madrid", "Split", "Budapest", "Reykjavik", "Warsaw"]
H, M, S, B, R, W = range(6)

# Allowed direct flights (directed). For undirected pairs, add both directions.
allowed_pairs = set()
def add_undirected(a, b):
    allowed_pairs.add((a, b))
    allowed_pairs.add((b, a))

# Given connections
add_undirected(H, R)
add_undirected(B, W)
add_undirected(M, S)
add_undirected(H, S)
add_undirected(H, M)
add_undirected(H, B)
add_undirected(R, W)
add_undirected(H, W)
add_undirected(M, B)
add_undirected(B, R)
add_undirected(M, W)
add_undirected(W, S)
# Directed: from Reykjavik to Madrid
allowed_pairs.add((R, M))

days = list(range(1, 15))  # 1..14

# Z3 variables: city at end of each day
c = [Int(f"c_{d}") for d in days]

s = Solver()

# Domain constraints
for d in days:
    s.add(And(c[d-1] >= 0, c[d-1] < 6))

# Helper: is flight on day d (d >= 2)
is_flight = [None] + [Int(f"flight_{d}") for d in range(2, 15)]
for d in range(2, 15):
    s.add(Or(is_flight[d] == 0, is_flight[d] == 1))
    s.add(is_flight[d] == If(c[d-2] != c[d-1], 1, 0))
    # If flight occurs, it must be along an allowed direct edge
    allowed_edge_disj = Or(*[And(c[d-2] == i, c[d-1] == j) for (i, j) in allowed_pairs])
    s.add(Or(c[d-2] == c[d-1], allowed_edge_disj))

# Exactly 5 flights (transitions)
s.add(Sum([is_flight[d] for d in range(2, 15)]) == 5)

# Presence: day counts for each city
# present[d][city] = 1 if day d counts for 'city' (being end-of-day in city, or departure from city on day d)
present = [[Int(f"present_{d}_{city}") for city in range(6)] for d in days]
for d in days:
    for city in range(6):
        if d == 1:
            s.add(Or(present[d-1][city] == 0, present[d-1][city] == 1))
            s.add(present[d-1][city] == If(c[d-1] == city, 1, 0))
        else:
            # present if end-of-day is city OR departure from city on this day
            s.add(Or(present[d-1][city] == 0, present[d-1][city] == 1))
            s.add(present[d-1][city] ==
                  If(Or(c[d-1] == city, c[d-2] == city), 1, 0))

# Required total days per city
req_days = {H: 2, W: 3, M: 4, S: 4, B: 4, R: 2}
for city, req in req_days.items():
    s.add(Sum([present[d-1][city] for d in days]) == req)

# Must be present in Helsinki on days 1 and 2 (workshop)
s.add(present[0][H] == 1)  # day 1
s.add(present[1][H] == 1)  # day 2

# Must be present in Reykjavik on days 8 and 9 (meet friend)
s.add(present[7][R] == 1)  # day 8
s.add(present[8][R] == 1)  # day 9

# Must be present in Warsaw on days 9, 10, 11 (visit relatives)
s.add(present[8][W] == 1)  # day 9
s.add(present[9][W] == 1)  # day 10
s.add(present[10][W] == 1) # day 11

# Also, Helsinki must be on day 1 (since presence on day 1 only possible if c1 is Helsinki)
s.add(c[0] == H)

# Solve
if s.check() != sat:
    raise RuntimeError("No feasible itinerary found")

m = s.model()
itinerary = []
for d in days:
    city_idx = m.evaluate(c[d-1]).as_long()
    itinerary.append({"day": d, "city": cities[city_idx]})

print(json.dumps({"itinerary": itinerary}, indent=2))