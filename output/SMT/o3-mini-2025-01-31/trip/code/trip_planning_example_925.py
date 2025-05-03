from z3 import *

# City indices and durations:
# 0: Vilnius   (5 days)
# 1: Krakow    (5 days)
# 2: Split     (5 days) – Meet a friend in Split between day 13 and day 17, so force Split’s block to [13,17] (arrival == 13)
# 3: Nice      (3 days) – Wedding in Nice between day 22 and day 24, so force Nice’s block to [22,24] (arrival == 22)
# 4: Helsinki  (5 days)
# 5: Venice    (2 days)
# 6: Valencia  (5 days)
cities = ["Vilnius", "Krakow", "Split", "Nice", "Helsinki", "Venice", "Valencia"]
durations = [5, 5, 5, 3, 5, 2, 5]

# Total raw days = 5 + 5 + 5 + 3 + 5 + 2 + 5 = 30 days.
# There are 6 transitions (the departure day is the same as the next arrival)
# so overall trip duration = 30 - 6 = 24 days.

# Allowed direct flights (bidirectional, except "from Krakow to Vilnius" is given as one‐way but treated as bidirectional):
# 1. Krakow and Split       -> {1, 2}
# 2. Split and Helsinki      -> {2, 4}
# 3. Venice and Nice         -> {5, 3}
# 4. Helsinki and Nice       -> {4, 3}
# 5. Vilnius and Helsinki    -> {0, 4}
# 6. Valencia and Krakow      -> {6, 1}
# 7. Krakow and Vilnius      -> {1, 0}
# 8. Vilnius and Split       -> {0, 2}
# 9. Helsinki and Venice     -> {4, 5}
# 10. Krakow and Helsinki    -> {1, 4}
direct_flights = [
    ("Krakow", "Split"),
    ("Split", "Helsinki"),
    ("Venice", "Nice"),
    ("Helsinki", "Nice"),
    ("Vilnius", "Helsinki"),
    ("Valencia", "Krakow"),
    ("Krakow", "Vilnius"),
    ("Vilnius", "Split"),
    ("Helsinki", "Venice"),
    ("Krakow", "Helsinki")
]

# Map city names to indices.
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Build allowed unordered pairs.
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Create Z3 solver.
s = Solver()
n = len(cities)

# Define variables for the visitation order (a permutation of city indices).
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit slot.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the visited city is c then departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 24.
s.add(departures[n-1] == 24)

# Time-specific event constraints:
# Force Split's 5-day block to be [13,17] (arrival == 13)
for i in range(n):
    s.add(If(order[i] == city_to_idx["Split"],
             arrivals[i] == 13,
             True))

# Force Nice's 3-day block to be [22,24] (arrival == 22)
for i in range(n):
    s.add(If(order[i] == city_to_idx["Nice"],
             arrivals[i] == 22,
             True))

# Connectivity constraints:
# Each consecutive pair of cities in the order must be connected by an allowed direct flight.
for i in range(n - 1):
    conn_options = []
    for pair in allowed_pairs:
        pair_list = list(pair)
        a, b = pair_list[0], pair_list[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(conn_options))

# Solve the constraints and output the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        itinerary.append((cities[city_idx], arr_day, dep_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:10s} : [{a}, {d}]")
else:
    print("No solution found")