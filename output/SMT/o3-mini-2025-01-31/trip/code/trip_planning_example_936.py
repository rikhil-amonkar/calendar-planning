from z3 import *

# We have 7 cities with the following durations and event constraints:
# 0: Budapest   (3 days) – Conference in Budapest between day 5 and day 7 → force arrival = 5 (block: [5,7])
# 1: Riga       (4 days)
# 2: Dubrovnik  (4 days)
# 3: Athens     (4 days)
# 4: Stockholm  (2 days) – Meet a friend in Stockholm between day 11 and day 12 → force arrival = 11 (block: [11,12])
# 5: Bucharest  (5 days)
# 6: Vienna     (5 days)
cities = ["Budapest", "Riga", "Dubrovnik", "Athens", "Stockholm", "Bucharest", "Vienna"]
durations = [3, 4, 4, 4, 2, 5, 5]

# Total raw days = 3+4+4+4+2+5+5 = 27.
# With 6 transitions (each consecutive pair sharing one day), overall trip duration = 27 - 6 = 21 days.

# Allowed direct flights (bidirectional):
# 1. Vienna and Riga         -> {Vienna, Riga} -> {6, 1}
# 2. Stockholm and Riga       -> {Stockholm, Riga} -> {4, 1}
# 3. Dubrovnik and Athens     -> {Dubrovnik, Athens} -> {2, 3}
# 4. Vienna and Athens        -> {Vienna, Athens} -> {6, 3}
# 5. Bucharest and Budapest   -> {Bucharest, Budapest} -> {5, 0}
# 6. from Athens to Riga       -> {Athens, Riga} -> {3, 1}  (treat as bidirectional)
# 7. Bucharest and Athens     -> {Bucharest, Athens} -> {5, 3}
# 8. Vienna and Dubrovnik     -> {Vienna, Dubrovnik} -> {6, 2}
# 9. Budapest and Vienna      -> {Budapest, Vienna} -> {0, 6}
# 10. Bucharest and Vienna    -> {Bucharest, Vienna} -> {5, 6}
# 11. Stockholm and Athens    -> {Stockholm, Athens} -> {4, 3}
# 12. Bucharest and Riga      -> {Bucharest, Riga} -> {5, 1}
# 13. Vienna and Stockholm    -> {Vienna, Stockholm} -> {6, 4}
# 14. Stockholm and Dubrovnik -> {Stockholm, Dubrovnik} -> {4, 2}
direct_flights = [
    ("Vienna", "Riga"),
    ("Stockholm", "Riga"),
    ("Dubrovnik", "Athens"),
    ("Vienna", "Athens"),
    ("Bucharest", "Budapest"),
    ("Athens", "Riga"),
    ("Bucharest", "Athens"),
    ("Vienna", "Dubrovnik"),
    ("Budapest", "Vienna"),
    ("Bucharest", "Vienna"),
    ("Stockholm", "Athens"),
    ("Bucharest", "Riga"),
    ("Vienna", "Stockholm"),
    ("Stockholm", "Dubrovnik")
]

# Map city names to indices.
city_to_idx = { city: idx for idx, city in enumerate(cities) }

# Build allowed unordered flight pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Set up the Z3 solver.
s = Solver()
n = len(cities)

# Define the visitation order as a permutation of city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the visited city is c, then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day:
# arrival of visit i+1 == departure of visit i.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 21.
s.add(departures[n-1] == 21)

# Time-specific event constraints:
# Budapest (city 0): Conference between day 5 and day 7 → force arrival = 5.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Budapest"],
             arrivals[i] == 5,
             True))
# Stockholm (city 4): Meet a friend between day 11 and day 12 → force arrival = 11.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Stockholm"],
             arrivals[i] == 11,
             True))

# Connectivity constraints:
# Each consecutive pair of cities must be connected by a direct flight.
for i in range(n-1):
    flight_options = []
    for pair in allowed_pairs:
        pair_list = list(pair)
        a, b = pair_list[0], pair_list[1]
        flight_options.append(And(order[i] == a, order[i+1] == b))
        flight_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(*flight_options))

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