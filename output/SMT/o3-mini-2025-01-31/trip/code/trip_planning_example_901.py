from z3 import *

# City indices and durations:
# 0: Prague (2 days)
# 1: Lyon   (3 days)
# 2: Porto  (5 days)
# 3: Berlin (4 days)
# 4: Stuttgart (2 days)
# 5: Munich (2 days)
# 6: Paris  (5 days)
cities = ["Prague", "Lyon", "Porto", "Berlin", "Stuttgart", "Munich", "Paris"]
durations = [2, 3, 5, 4, 2, 2, 5]

# Direct flights (assumed bidirectional) as given:
direct_flights = [
    ("Paris", "Munich"),
    ("Stuttgart", "Berlin"),
    ("Porto", "Berlin"),
    ("Stuttgart", "Paris"),
    ("Munich", "Berlin"),
    ("Prague", "Munich"),
    ("Prague", "Lyon"),
    ("Porto", "Lyon"),
    ("Paris", "Lyon"),
    ("Paris", "Prague"),
    ("Paris", "Berlin"),
    ("Porto", "Munich"),
    ("Lyon", "Munich"),
    ("Porto", "Stuttgart"),
    ("Porto", "Paris")
]

# Create mapping from city name to index
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed pairs as a set of frozensets (order doesn’t matter)
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

# Link the stay length (duration) with each city.
for i in range(n):
    cases = []
    for city in range(n):
        # When city is chosen in position i, its departure equals arrival + duration - 1
        cases.append(If(order[i] == city, departures[i] == arrivals[i] + durations[city] - 1, True))
    s.add(And(cases))

# For positions after the first, arrival equals previous departure (overnight flight)
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip finishes at day 17.
s.add(departures[n-1] == 17)

# Extra conditions:
# 1. In Lyon (city index 1) you attend a wedding between day 11 and 13.
#    Lyon's block is [arrival, arrival+2] so we require that:
#         arrival <= 13 and arrival+2 >= 11.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Lyon"],
             And(arrivals[i] <= 13, arrivals[i] + 2 >= 11),
             True))

# 2. In Berlin (city index 3) you meet a friend between day 14 and 17.
#    Berlin's block is [arrival, arrival+3] so:
#         arrival <= 17 and arrival+3 >= 14.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Berlin"],
             And(arrivals[i] <= 17, arrivals[i] + 3 >= 14),
             True))

# 3. In Stuttgart (city index 4) you must attend a conference on days 5 and 6.
#    Stuttgart's block is [arrival, arrival+1] and to cover days 5 and 6, the arrival must equal 5.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Stuttgart"],
             arrivals[i] == 5,
             True))

# Connectivity constraints: Consecutive cities must have a direct flight.
for i in range(n-1):
    pair_cases = []
    for p in allowed_pairs:
        lst = list(p)
        # p is a frozenset with two cities;
        # allow either [a, b] or [b, a]
        p0, p1 = lst[0], lst[1]
        pair_cases.append(And(order[i] == p0, order[i+1] == p1))
        pair_cases.append(And(order[i] == p1, order[i+1] == p0))
    s.add(Or(pair_cases))

# Check for a solution and print an itinerary.
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
        print(f"  {city:10s} [{a}, {d}]")
else:
    print("No solution found")