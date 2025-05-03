from z3 import *

# City indices and durations:
# 0: Valencia   (2 days)
# 1: Milan      (4 days)
# 2: Oslo       (5 days)
# 3: Santorini  (5 days)
# 4: Berlin     (2 days)
# 5: Reykjavik  (4 days)
# 6: Vienna     (4 days)
cities = ["Valencia", "Milan", "Oslo", "Santorini", "Berlin", "Reykjavik", "Vienna"]
durations = [2, 4, 5, 5, 2, 4, 4]

# Total raw days = 2+4+5+5+2+4+4 = 26.
# Since we share a flight day between consecutive cities (6 shared flight days), total trip = 26-6 = 20 days.
# Flight schedule: only direct flights (bidirectional) are allowed as given:
direct_flights = [
    ("Santorini", "Oslo"),
    ("Santorini", "Valencia"),
    ("Santorini", "Milan"),
    ("Milan", "Vienna"),
    ("Berlin", "Valencia"),
    ("Berlin", "Vienna"),
    ("Berlin", "Reykjavik"),
    ("Oslo", "Vienna"),
    ("Santorini", "Vienna"),
    ("Milan", "Santorini"),
    ("Reykjavik", "Vienna"),
    ("Valencia", "Vienna"),
    ("Milan", "Reykjavik"),
    ("Oslo", "Reykjavik"),
    ("Berlin", "Oslo"),
    ("Berlin", "Milan"),
    ("Milan", "Oslo")
]

# Create mapping from city name to index
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed pairs as a set of frozensets (order does not matter)
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

s = Solver()
n = len(cities)

# The itinerary ordering: order[i] is the city visited in the i-th slot.
order = [Int("order_%i" % i) for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Arrival and departure days for each city in the itinerary.
# Arrival day for the 1st city is 1.
arrivals = [Int("arr_%i" % i) for i in range(n)]
departures = [Int("dep_%i" % i) for i in range(n)]
s.add(arrivals[0] == 1)

# Link each city's duration to its departure day.
for i in range(n):
    cases = []
    for city in range(n):
        # For city chosen in position i, departure equals arrival + duration - 1.
        cases.append(If(order[i] == city, departures[i] == arrivals[i] + durations[city] - 1, True))
    s.add(And(cases))

# For positions after the first, arrival equals the previous departure (overnight flight reuse).
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip ends at day 20.
s.add(departures[n-1] == 20)

# Extra conditions:

# 1. In Valencia (city index 0) you meet your friends between day 2 and day 3.
#    Valencia's block is 2 days: [arrival, arrival+1]. The block must overlap with [2,3].
#    This is ensured if arrival <= 3 and (arrival+1) >= 2.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Valencia"],
             And(arrivals[i] <= 3, arrivals[i] + 1 >= 2),
             True))

# 2. In Vienna (city index 6) you attend a workshop between day 17 and day 20.
#    Vienna's block is 4 days: [arrival, arrival+1, arrival+2, arrival+3]. It must cover [17,20].
#    So we require arrival <= 20 and arrival+3 >= 17.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Vienna"],
             And(arrivals[i] <= 20, arrivals[i] + 3 >= 17),
             True))

# Connectivity constraints: successive cities in the itinerary must be linked by a direct flight.
for i in range(n-1):
    pair_conditions = []
    for p in allowed_pairs:
        lst = list(p)
        a, b = lst[0], lst[1]
        pair_conditions.append(And(order[i] == a, order[i+1] == b))
        pair_conditions.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(pair_conditions))

# Check for a solution and print the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_index = m[order[i]].as_long()
        a_day = m[arrivals[i]].as_long()
        d_day = m[departures[i]].as_long()
        itinerary.append((cities[city_index], a_day, d_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:12s} [{a}, {d}]")
else:
    print("No solution found")