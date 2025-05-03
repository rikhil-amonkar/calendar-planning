from z3 import *

# City indices and durations:
# 0: Prague     (5 days)
# 1: Munich     (3 days)
# 2: Berlin     (2 days) – Friends meeting in Berlin between day 15 and day 16 → force Berlin's block to [15,16] (arrival = 15)
# 3: Vilnius    (5 days)
# 4: Nice       (3 days)
# 5: Stuttgart  (3 days) – Relatives in Stuttgart between day 1 and day 3 → force Stuttgart's block to [1,3] (arrival = 1)
# 6: Lisbon     (5 days)
cities = ["Prague", "Munich", "Berlin", "Vilnius", "Nice", "Stuttgart", "Lisbon"]
durations = [5, 3, 2, 5, 3, 3, 5]

# Total raw days = 5+3+2+5+3+3+5 = 26.
# With 6 transitions (shared days) overall trip duration = 26 - 6 = 20 days.

# Allowed direct flights (bidirectional):
# 1. from Vilnius to Munich       -> {Vilnius, Munich}       -> {3, 1}
# 2. Munich and Nice              -> {Munich, Nice}          -> {1, 4}
# 3. Stuttgart and Berlin         -> {Stuttgart, Berlin}     -> {5, 2}
# 4. Munich and Berlin            -> {Munich, Berlin}        -> {1, 2}
# 5. Stuttgart and Lisbon         -> {Stuttgart, Lisbon}     -> {5, 6}
# 6. Lisbon and Prague            -> {Lisbon, Prague}        -> {6, 0}
# 7. Berlin and Vilnius           -> {Berlin, Vilnius}       -> {2, 3}
# 8. Prague and Munich            -> {Prague, Munich}        -> {0, 1}
# 9. Lisbon and Munich            -> {Lisbon, Munich}        -> {6, 1}
# 10. Lisbon and Nice             -> {Lisbon, Nice}          -> {6, 4}
# 11. Nice and Berlin             -> {Nice, Berlin}          -> {4, 2}
# 12. Lisbon and Berlin           -> {Lisbon, Berlin}        -> {6, 2}
direct_flights = [
    ("Vilnius", "Munich"),
    ("Munich", "Nice"),
    ("Stuttgart", "Berlin"),
    ("Munich", "Berlin"),
    ("Stuttgart", "Lisbon"),
    ("Lisbon", "Prague"),
    ("Berlin", "Vilnius"),
    ("Prague", "Munich"),
    ("Lisbon", "Munich"),
    ("Lisbon", "Nice"),
    ("Nice", "Berlin"),
    ("Lisbon", "Berlin")
]

# Create a mapping from city names to indices.
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Build allowed unordered flight pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Set up the Z3 solver.
s = Solver()
n = len(cities)

# Create a permutation for the visit order.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(*order))

# Create arrival and departure variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, set departure = arrival + duration - 1 for whichever city is visited.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Ensure consecutive visits share the transit day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 20.
s.add(departures[n-1] == 20)

# Time-specific event constraints:
# Stuttgart: Relatives between day 1 and 3 → force Stuttgart's arrival = 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Stuttgart"],
             arrivals[i] == 1,
             True))

# Berlin: Meet friends between day 15 and 16 → force Berlin's arrival = 15.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Berlin"],
             arrivals[i] == 15,
             True))

# Connectivity constraints: each consecutive pair of cities must be connected by a direct flight.
for i in range(n - 1):
    conn_options = []
    for pair in allowed_pairs:
        pair_list = list(pair)
        a, b = pair_list[0], pair_list[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(*conn_options))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        itinerary.append((cities[city_idx], arr_day, dep_day))
    for city, a, d in itinerary:
        print(f"  {city:10s}: [{a}, {d}]")
else:
    print("No solution found")