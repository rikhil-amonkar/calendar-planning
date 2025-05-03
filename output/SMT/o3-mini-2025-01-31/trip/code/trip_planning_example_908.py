from z3 import *

# City indices and durations:
# 0: Bucharest (2 days)
# 1: Stockholm (3 days)
# 2: Split     (2 days)
# 3: Lyon      (4 days)  -- relatives visit in Lyon between day 3 and day 6
# 4: Krakow    (5 days)
# 5: Naples    (2 days)
# 6: Tallinn   (4 days)  -- workshop in Tallinn between day 13 and day 16
cities = ["Bucharest", "Stockholm", "Split", "Lyon", "Krakow", "Naples", "Tallinn"]
durations = [2, 3, 2, 4, 5, 2, 4]

# Sum of durations = 2+3+2+4+5+2+4 = 22. With 6 transitions (each sharing one day),
# the overall trip length is 22 - 6 = 16 days.

# Allowed direct flights (bidirectional):
direct_flights = [
    ("Stockholm", "Tallinn"),
    ("Krakow", "Stockholm"),
    ("Bucharest", "Lyon"),
    ("Naples", "Split"),
    ("Naples", "Bucharest"),
    ("Split", "Krakow"),
    ("Lyon", "Split"),
    ("Split", "Stockholm")
]

# Map city names to their indices.
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build the set of allowed unordered pairs (flights are bidirectional)
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

s = Solver()
n = len(cities)

# Define the order in which cities are visited:
order = [Int("order_%i" % i) for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure days for each visit.
arrivals = [Int("arr_%i" % i) for i in range(n)]
departures = [Int("dep_%i" % i) for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# Link each city's duration with its departure day:
# If a city with duration d is visited in slot i, then: departure = arrival + d - 1.
for i in range(n):
    conds = []
    for city in range(n):
        conds.append(If(order[i] == city, departures[i] == arrivals[i] + durations[city] - 1, True))
    s.add(And(conds))

# Consecutive visits share the transit day (i.e. flight day):
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip ends on day 16.
s.add(departures[n-1] == 16)

# Extra time-specific constraints:
# 1. Relatives in Lyon (city index 3) between day 3 and day 6.
# Lyon's block is 4 days: [arr, arr+3]. It must intersect [3,6]:
#   This is ensured by: arr <= 6 and arr+3 >= 3.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Lyon"],
             And(arrivals[i] <= 6, arrivals[i] + 3 >= 3),
             True))

# 2. Workshop in Tallinn (city index 6) between day 13 and day 16.
# Tallinn's block is 4 days: [arr, arr+3]. It must intersect [13,16]:
#   So, arr <= 16 and arr+3 >= 13.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Tallinn"],
             And(arrivals[i] <= 16, arrivals[i] + 3 >= 13),
             True))

# Connectivity constraints: consecutive cities must be connected by a direct flight.
for i in range(n - 1):
    trans_options = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        trans_options.append(And(order[i] == a, order[i+1] == b))
        trans_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(trans_options))

# Check for a solution and print the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    # Retrieve cities in order with their arrival and departure days.
    for i in range(n):
        city_idx = m[order[i]].as_long()
        a_day = m[arrivals[i]].as_long()
        d_day = m[departures[i]].as_long()
        itinerary.append((cities[city_idx], a_day, d_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:10s} [{a}, {d}]")
else:
    print("No solution found")