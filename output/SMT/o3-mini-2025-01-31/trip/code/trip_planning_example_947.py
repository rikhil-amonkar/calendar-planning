from z3 import *

# Define the 7 cities, their durations, and any event constraints:
# 0: Lyon      (5 days)
# 1: London    (2 days)
# 2: Rome      (4 days) – Annual show from day 10 to 13, so force arrival = 10.
# 3: Budapest  (5 days) – Meet friend between day 1 and 5, so force arrival = 1.
# 4: Dubrovnik (3 days) – Meet friends between day 13 and 15, so force arrival = 13.
# 5: Seville   (5 days)
# 6: Vienna    (5 days)
#
# Total raw days = 5 + 2 + 4 + 5 + 3 + 5 + 5 = 29.
# With 6 transitions (each consecutive visit shares one day),
# the overall trip length = 29 - 6 = 23 days.
cities = ["Lyon", "London", "Rome", "Budapest", "Dubrovnik", "Seville", "Vienna"]
durations = [5, 2, 4, 5, 3, 5, 5]

# Allowed direct flights (bidirectional):
# 1. London and Rome       -> {London, Rome}          -> {1, 2}
# 2. Rome and Vienna       -> {Rome, Vienna}          -> {2, 6}
# 3. Rome and Dubrovnik    -> {Rome, Dubrovnik}       -> {2, 4}
# 4. London and Vienna     -> {London, Vienna}        -> {1, 6}
# 5. London and Lyon       -> {London, Lyon}          -> {1, 0}
# 6. Dubrovnik and Vienna  -> {Dubrovnik, Vienna}     -> {4, 6}
# 7. Lyon and Rome         -> {Lyon, Rome}            -> {0, 2}
# 8. Vienna and Seville    -> {Vienna, Seville}       -> {6, 5}
# 9. Budapest and Vienna   -> {Budapest, Vienna}      -> {3, 6}
# 10. Rome and Seville     -> {Rome, Seville}         -> {2, 5}
# 11. Lyon and Vienna      -> {Lyon, Vienna}          -> {0, 6}
# 12. Budapest and Rome    -> {Budapest, Rome}        -> {3, 2}
# 13. Budapest and London  -> {Budapest, London}      -> {3, 1}
direct_flights = [
    ("London", "Rome"),
    ("Rome", "Vienna"),
    ("Rome", "Dubrovnik"),
    ("London", "Vienna"),
    ("London", "Lyon"),
    ("Dubrovnik", "Vienna"),
    ("Lyon", "Rome"),
    ("Vienna", "Seville"),
    ("Budapest", "Vienna"),
    ("Rome", "Seville"),
    ("Lyon", "Vienna"),
    ("Budapest", "Rome"),
    ("Budapest", "London")
]

# Map city names to indices.
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Build allowed flight connections as unordered pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # number of cities, 7

# Define visitation order as a permutation of indices [0, n-1].
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visited city at slot i, the departure day is:
#    departure = arrival + duration - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share a transit day:
# arrival[i+1] == departure[i] for all i.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 23.
s.add(departures[n-1] == 23)

# Time-specific event constraints:
# Budapest (city index 3): meet friend between day 1 and 5 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Budapest"], arrivals[i] == 1, True))
# Rome (city index 2): annual show from day 10 to 13 → force arrival = 10.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Rome"], arrivals[i] == 10, True))
# Dubrovnik (city index 4): meet friends between day 13 and 15 → force arrival = 13.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Dubrovnik"], arrivals[i] == 13, True))

# Connectivity constraints:
# Each consecutive pair in the itinerary must be connected by a direct flight.
for i in range(n - 1):
    flight_options = []
    for pair in allowed_pairs:
        plist = list(pair)
        a, b = plist[0], plist[1]
        flight_options.append(And(order[i] == a, order[i+1] == b))
        flight_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(*flight_options))

# Solve and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_idx]:10s}: [{a_day}, {d_day}]")
else:
    print("No solution found")