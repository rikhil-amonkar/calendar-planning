from z3 import *

# City indices and durations:
# 0: Athens    (2 days)
# 1: Mykonos   (2 days)
# 2: Santorini (5 days) - workshop between day 4 and day 8
# 3: Milan     (5 days) - annual show from day 14 to day 18
# 4: Warsaw    (5 days)
# 5: Stockholm (4 days)
# 6: Brussels  (2 days) - visit relatives between day 9 and day 10
cities = ["Athens", "Mykonos", "Santorini", "Milan", "Warsaw", "Stockholm", "Brussels"]
durations = [2, 2, 5, 5, 5, 4, 2]

# Total raw days: 2+2+5+5+5+4+2 = 25.
# With 6 transitions (overnight flight days shared), overall trip = 25 - 6 = 19 days.

# Allowed direct flights (bidirectional):
direct_flights = [
    ("Stockholm", "Milan"),
    ("Athens", "Brussels"),
    ("Santorini", "Athens"),
    ("Stockholm", "Brussels"),
    ("Stockholm", "Athens"),
    ("Stockholm", "Santorini"),  # given as "from Stockholm to Santorini" but assume bidirectional
    ("Stockholm", "Warsaw"),
    ("Brussels", "Warsaw"),
    ("Warsaw", "Milan"),
    ("Athens", "Mykonos"),
    ("Athens", "Milan"),
    ("Santorini", "Milan"),
    ("Brussels", "Milan"),
    ("Milan", "Mykonos"),
    ("Athens", "Warsaw")
]

# Map city names to indices.
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed unordered pairs.
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

s = Solver()
n = len(cities)

# Define the order (permutation) in which cities are visited.
order = [Int("order_%i" % i) for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure days for each visit.
arrivals = [Int("arr_%i" % i) for i in range(n)]
departures = [Int("dep_%i" % i) for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit i, set departure = arrival + duration - 1.
for i in range(n):
    conds = []
    for city in range(n):
        conds.append(If(order[i] == city, departures[i] == arrivals[i] + durations[city] - 1, True))
    s.add(And(conds))

# Consecutive cities share the flight (transition) day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 19.
s.add(departures[n-1] == 19)

# Extra time-specific constraints:
# Santorini (index 2): Workshop between day 4 and day 8.
# Santorini's 5-day block is [arr, arr+4]. It must intersect [4,8]:
#   arrival <= 8 and arrival+4 >= 4.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Santorini"],
             And(arrivals[i] <= 8, arrivals[i] + 4 >= 4),
             True))

# Milan (index 3): Annual show from day 14 to day 18.
# Milan's 5-day block [arr, arr+4] must intersect [14,18]:
#   arrival <= 18 and arrival+4 >= 14.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Milan"],
             And(arrivals[i] <= 18, arrivals[i] + 4 >= 14),
             True))

# Brussels (index 6): Visit relatives between day 9 and day 10.
# Brussels's 2-day block [arr, arr+1] must intersect [9,10]:
#   arrival <= 10 and arrival+1 >= 9.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Brussels"],
             And(arrivals[i] <= 10, arrivals[i] + 1 >= 9),
             True))

# Connectivity: Consecutive cities must be connected by a direct flight.
for i in range(n-1):
    trans_options = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        trans_options.append(And(order[i] == a, order[i+1] == b))
        trans_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(trans_options))

# Solve the constraints and print the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_idx = m[order[i]].as_long()
        a_day = m[arrivals[i]].as_long()
        d_day = m[departures[i]].as_long()
        itinerary.append((cities[city_idx], a_day, d_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, start, end in itinerary:
        print(f"  {city:12s} [{start}, {end}]")
else:
    print("No solution found")