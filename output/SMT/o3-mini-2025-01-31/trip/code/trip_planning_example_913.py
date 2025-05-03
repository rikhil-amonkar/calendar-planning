from z3 import *

# City indices and durations:
# 0: Milan      (3 days)
# 1: Geneva     (5 days)
# 2: Reykjavik  (4 days) – Friend meeting: must be in Reykjavik between day 2 and day 5.
# 3: Santorini  (5 days) – Wedding: must be in Santorini between day 7 and day 11.
# 4: Helsinki   (2 days)
# 5: Vilnius    (4 days)
# 6: Split      (3 days)
cities = ["Milan", "Geneva", "Reykjavik", "Santorini", "Helsinki", "Vilnius", "Split"]
durations = [3, 5, 4, 5, 2, 4, 3]

# Total raw days = 3+5+4+5+2+4+3 = 26.
# With 6 transit days (shared flight days) the overall trip lasts 26 - 6 = 20 days.

# Allowed direct flights (bidirectional):
# - Split and Vilnius
# - Reykjavik and Milan
# - Helsinki and Reykjavik
# - Milan and Santorini
# - Milan and Split
# - Helsinki and Split
# - Helsinki and Geneva
# - Santorini and Geneva
# - Helsinki and Milan
# - Milan and Vilnius
direct_flights = [
    ("Split", "Vilnius"),
    ("Reykjavik", "Milan"),
    ("Helsinki", "Reykjavik"),
    ("Milan", "Santorini"),
    ("Milan", "Split"),
    ("Helsinki", "Split"),
    ("Helsinki", "Geneva"),
    ("Santorini", "Geneva"),
    ("Helsinki", "Milan"),
    ("Milan", "Vilnius")
]

# Create a mapping from city name to index.
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed pairs (as unordered sets, since flights are bidirectional).
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

s = Solver()
n = len(cities)

# Define the order in which cities are visited: a permutation of [0,..,6].
order = [Int("order_%i" % i) for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure days for each visit.
arrivals = [Int("arr_%i" % i) for i in range(n)]
departures = [Int("dep_%i" % i) for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For a visit in slot i, if the city has duration d then:
# departure = arrival + d - 1.
for i in range(n):
    cs = []
    for city in range(n):
        cs.append(If(order[i] == city, departures[i] == arrivals[i] + durations[city] - 1, True))
    s.add(And(cs))

# Consecutive visits share the transit (flight) day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip ends on day 20.
s.add(departures[n-1] == 20)

# Time-specific constraints:

# 1. Reykjavik (index 2): Friend meeting between day 2 and day 5.
# Reykjavik's 4-day block is [a, a+3]. To have at least one day between day2 and day5:
# enforce:  a <= 5  and  a+3 >= 2.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Reykjavik"],
             And(arrivals[i] <= 5, arrivals[i] + 3 >= 2),
             True))

# 2. Santorini (index 3): Wedding between day 7 and day 11.
# Santorini's 5-day block is [a, a+4]. To ensure being present during the wedding period:
# enforce:  a <= 11  and  a+4 >= 7.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Santorini"],
             And(arrivals[i] <= 11, arrivals[i] + 4 >= 7),
             True))

# Connectivity constraints: consecutive cities must be connected by a direct flight.
for i in range(n-1):
    conn_options = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(conn_options))

# Solve and print the itinerary if found.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_index = m[order[i]].as_long()
        a_day = m[arrivals[i]].as_long()
        d_day = m[departures[i]].as_long()
        itinerary.append((cities[city_index], a_day, d_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, start, end in itinerary:
        print(f"  {city:10s} [{start}, {end}]")
else:
    print("No solution found")