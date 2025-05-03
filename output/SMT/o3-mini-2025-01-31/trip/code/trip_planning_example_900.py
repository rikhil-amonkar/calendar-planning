from z3 import *

# We label the cities with indices and store their durations:
# 0: Oslo (3 days)
# 1: Porto (5 days)
# 2: Hamburg (2 days)
# 3: Valencia (2 days)
# 4: Vienna (3 days)
# 5: Rome (4 days)
# 6: Berlin (2 days)
cities = ["Oslo", "Porto", "Hamburg", "Valencia", "Vienna", "Rome", "Berlin"]
durations = [3, 5, 2, 2, 3, 4, 2]  # required stay lengths in each city

# Allowed flights (since flights are direct and assumed to be two‐way,
# we use a set of frozensets for unordered pairs)
allowed_pairs = set()
# add each allowed pair (order does not matter as we assume flights go both ways)
direct_flights = [
    ("Berlin","Rome"), ("Berlin","Valencia"), ("Hamburg","Vienna"), ("Berlin","Porto"),
    ("Oslo","Porto"), ("Rome","Vienna"), ("Berlin","Oslo"), ("Rome","Hamburg"),
    ("Porto","Valencia"), ("Oslo","Vienna"), ("Oslo","Hamburg"), ("Rome","Valencia"),
    ("Vienna","Valencia"), ("Oslo","Rome"), ("Hamburg","Porto"), ("Berlin","Vienna"),
    ("Vienna","Porto")
]
# create a mapping from city name to index:
city_to_idx = { name: idx for idx, name in enumerate(cities) }
for (c1, c2) in direct_flights:
    allowed_pairs.add(frozenset({ city_to_idx[c1], city_to_idx[c2] }))

# Create the solver
s = Solver()

n = len(cities)

# permutation: order[i] is the city visited in the i-th slot.
order = [Int("order_%i" % i) for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# We'll “calculate” the arrival day for each city in the itinerary.
# By convention, the first city is entered on day 1.
arrivals = [Int("arr_%i" % i) for i in range(n)]
# The departure day from a city is arrival + duration - 1.
departures = [Int("dep_%i" % i) for i in range(n)]

s.add(arrivals[0] == 1)
s.add(departures[0] == arrivals[0] + durations[0] - 1)  # careful: durations are not indexed by order!
# We cannot “directly” add durations[ order[0] ] because order[0] is an IntVar.
# Instead we do a loop later to force the linking.

# To “link” the stay length with the chosen city we enforce for each position
# that the departure equals arrival + (duration of that city) -1.
for i in range(n):
    # Use a case-split for each possible city in position i.
    cases = []
    for city in range(n):
        cases.append(If(order[i] == city, departures[i] == arrivals[i] + durations[city] - 1, True))
    s.add(And(cases))

# For positions after the first, the arrival of the next city is the same as
# the departure of the previous city. (Flights happen “overnight”, so the arrival day is re‐used.)
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 15:
s.add(departures[n-1] == 15)

# Now add the extra requirements:
# 1. In Oslo (city 0), you want 3 days and you must attend a workshop between day 2 and 4.
#    That means the Oslo block, which is [arrival, arrival+2] (since 3 days) must include one day in {2,3,4}.
for i in range(n):
    # if city in position i is Oslo then arrival must be at most 4 so that [a, a+2] includes 2..4.
    s.add(If(order[i] == 0, arrivals[i] <= 4, True))
    # (Since arrival + 2 is always >= 2 when arrival>=1, we do not need an extra lower bound.)

# 2. In Porto (city 1) you want 5 days and you plan to visit relatives between day 10 and 14.
#    Porto’s block is [arrival, arrival+4] and to intersect [10,14] we must have arrival >= 6.
for i in range(n):
    s.add(If(order[i] == 1, arrivals[i] >= 6, True))

# 3. In Hamburg (city 2) you want 2 days and you must attend a conference on days 7 and 8.
#    Hamburg’s block is [arrival, arrival+1] and to cover both days 7 & 8 we force arrival == 7.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 7, True))

# Now add connectivity constraints: for i = 0..n-2, the consecutive cities must be connected by a direct flight.
for i in range(n-1):
    # We want: { order[i], order[i+1] } in allowed_pairs.
    # Since order[i] and order[i+1] are variables we can write a disjunction over all allowed pairs.
    pair_cases = []
    for p in allowed_pairs:
        # p is a frozenset of two cities; we need to force that order[i] and order[i+1] are exactly these two (in some order)
        listp = list(p)
        # There are two numbers in the set:
        p0 = listp[0]
        p1 = listp[1]
        pair_cases.append(And(order[i] == p0, order[i+1] == p1))
        pair_cases.append(And(order[i] == p1, order[i+1] == p0))
    s.add(Or(pair_cases))

# (Optionally, one may add symmetry-breaking constraints on the permutation.)

if s.check() == sat:
    m = s.model()
    # Reconstruct the itinerary with arrival and departure days.
    itinerary = []
    for i in range(n):
        city = m[order[i]].as_long()
        a = m[arrivals[i]].as_long()
        d = m[departures[i]].as_long()
        itinerary.append((cities[city], a, d))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:8s}  [{a}, {d}]")
else:
    print("No solution found")