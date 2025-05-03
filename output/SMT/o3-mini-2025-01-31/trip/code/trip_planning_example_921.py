from z3 import *

# City indices and durations:
# 0: Edinburgh  (2 days)
# 1: Vilnius    (5 days)
# 2: Santorini  (2 days) – Wedding between day 9 and day 10, so Santorini's 2‐day block must be [9,10]
# 3: Porto      (4 days)
# 4: Warsaw     (3 days) – Annual show between day 13 and day 15, so Warsaw's block must be [13,15]
# 5: Zurich     (4 days) – Meet a friend between day 10 and day 13, so Zurich's block must be [10,13]
# 6: Venice     (5 days)
cities = ["Edinburgh", "Vilnius", "Santorini", "Porto", "Warsaw", "Zurich", "Venice"]
durations = [2, 5, 2, 4, 3, 4, 5]

# Total raw days = 2 + 5 + 2 + 4 + 3 + 4 + 5 = 25.
# With 6 transitions (shared flight days), overall trip duration = 25 - 6 = 19 days.

# Allowed direct flights (bidirectional):
# - Porto and Zurich        -> {Porto, Zurich}         -> {3, 5}
# - Zurich and Warsaw        -> {Zurich, Warsaw}        -> {5, 4}
# - Zurich and Vilnius       -> {Zurich, Vilnius}       -> {5, 1}
# - Edinburgh and Venice     -> {Edinburgh, Venice}     -> {0, 6}
# - Porto and Edinburgh      -> {Porto, Edinburgh}      -> {3, 0}
# - Warsaw and Vilnius       -> {Warsaw, Vilnius}       -> {4, 1}
# - Venice and Santorini     -> {Venice, Santorini}     -> {6, 2}
# - Venice and Warsaw        -> {Venice, Warsaw}        -> {6, 4}
# - Santorini and Zurich     -> {Santorini, Zurich}     -> {2, 5}
# - Edinburgh and Zurich     -> {Edinburgh, Zurich}     -> {0, 5}
# - Venice and Zurich        -> {Venice, Zurich}        -> {6, 5}
# - Porto and Warsaw         -> {Porto, Warsaw}         -> {3, 4}
direct_flights = [
    ("Porto", "Zurich"),
    ("Zurich", "Warsaw"),
    ("Zurich", "Vilnius"),
    ("Edinburgh", "Venice"),
    ("Porto", "Edinburgh"),
    ("Warsaw", "Vilnius"),
    ("Venice", "Santorini"),
    ("Venice", "Warsaw"),
    ("Santorini", "Zurich"),
    ("Edinburgh", "Zurich"),
    ("Venice", "Zurich"),
    ("Porto", "Warsaw")
]

# Map city names to indices.
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed unordered pairs for connectivity.
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({ city_to_idx[a], city_to_idx[b] }))

# Create Z3 solver instance.
s = Solver()
n = len(cities)

# Define the visitation order as a permutation of 0..6.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit slot.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the city visited is c then its departure day is arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Adjacent visits share the transit day (i.e. the departure of one equals the arrival of the next).
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 19.
s.add(departures[n-1] == 19)

# Enforce time-specific event constraints:
# Santorini (index 2): Wedding between day 9 and day 10, so force Santorini's arrival == 9.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Santorini"],
             arrivals[i] == 9,
             True))

# Warsaw (index 4): Annual show from day 13 to day 15, so force Warsaw's arrival == 13.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Warsaw"],
             arrivals[i] == 13,
             True))

# Zurich (index 5): Meet a friend between day 10 and day 13, so force Zurich's arrival == 10.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Zurich"],
             arrivals[i] == 10,
             True))

# Connectivity constraints:
# Each consecutive pair of cities in the visitation order must be connected by a direct flight.
for i in range(n - 1):
    conn_options = []
    for pair in allowed_pairs:
        lst = list(pair)
        # Unpack the two cities from the allowed flight pair.
        a, b = lst[0], lst[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(conn_options))

# Solve the constraints and output the itinerary if one is found.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        itinerary.append((cities[city_idx], a_day, d_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:11s} : [{a}, {d}]")
else:
    print("No solution found")