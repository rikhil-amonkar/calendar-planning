from z3 import *

# City indices and durations:
# 0: Porto      (2 days)
# 1: Geneva     (2 days)
# 2: Munich     (2 days)
# 3: Tallinn    (3 days)
# 4: Vilnius    (4 days)
# 5: Budapest   (4 days)
# 6: Reykjavik  (4 days) – Annual show from day 1 to 4 → force arrival = 1.
#
# Total raw days = 2 + 2 + 2 + 3 + 4 + 4 + 4 = 21.
# With 6 overlaps between the 7 visits, overall trip length = 21 - 6 = 15 days.

cities = ["Porto", "Geneva", "Munich", "Tallinn", "Vilnius", "Budapest", "Reykjavik"]
durations = [2, 2, 2, 3, 4, 4, 4]

# Allowed direct flights:
# Note: Items with "from" indicate one-way flights.
# 1. from Vilnius to Munich:        (Vilnius -> Munich): (4,2)
# 2. Budapest and Munich:            bidirectional: (Budapest, Munich): (5,2) and (2,5)
# 3. from Tallinn to Vilnius:         one-way: (Tallinn -> Vilnius): (3,4)
# 4. Budapest and Geneva:            bidirectional: (Budapest, Geneva): (5,1) and (1,5)
# 5. Reykjavik and Munich:           bidirectional: (Reykjavik, Munich): (6,2) and (2,6)
# 6. Reykjavik and Budapest:         bidirectional: (Reykjavik, Budapest): (6,5) and (5,6)
# 7. Geneva and Porto:               bidirectional: (Geneva, Porto): (1,0) and (0,1)
# 8. Munich and Tallinn:             bidirectional: (Munich, Tallinn): (2,3) and (3,2)
# 9. Geneva and Munich:              bidirectional: (Geneva, Munich): (1,2) and (2,1)
# 10. Porto and Munich:              bidirectional: (Porto, Munich): (0,2) and (2,0)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. from Vilnius to Munich (one-way)
allowed_flights.append((4, 2))
# 2. Budapest and Munich (bidirectional)
add_bidirectional(5, 2)
# 3. from Tallinn to Vilnius (one-way)
allowed_flights.append((3, 4))
# 4. Budapest and Geneva (bidirectional)
add_bidirectional(5, 1)
# 5. Reykjavik and Munich (bidirectional)
add_bidirectional(6, 2)
# 6. Reykjavik and Budapest (bidirectional)
add_bidirectional(6, 5)
# 7. Geneva and Porto (bidirectional)
add_bidirectional(1, 0)
# 8. Munich and Tallinn (bidirectional)
add_bidirectional(2, 3)
# 9. Geneva and Munich (bidirectional)
add_bidirectional(1, 2)
# 10. Porto and Munich (bidirectional)
add_bidirectional(0, 2)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# We model the itinerary as a permutation of the city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit i, if the city c is visited then departure equals arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: the arrival day of visit i+1 must equal the departure day of visit i.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 15.
s.add(departures[n-1] == 15)

# Event-specific constraint:
# Reykjavik (city index 6): Annual show from day 1 to 4 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 1, True))

# Connectivity constraints:
# For each consecutive pair of visits, there must be a direct flight from the earlier city to the later city.
for i in range(n-1):
    # Build an OR condition over all allowed flight pairs (frm, to)
    s.add(Or([And(order[i] == frm, order[i+1] == to) for (frm, to) in allowed_flights]))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_idx]:10s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")