from z3 import *

# City indices and durations:
# 0: Budapest   (4 days)
# 1: Copenhagen (2 days)
# 2: Hamburg    (4 days)
# 3: Vienna     (5 days) – Conference in Vienna during day 1 and day 5 → force Vienna's block to [1,5] (arrival = 1)
# 4: Reykjavik  (2 days) – Wedding in Reykjavik between day 8 and day 9 → force Reykjavik's block to [8,9] (arrival = 8)
# 5: Split      (4 days) – Meet friends in Split between day 10 and day 13 → force Split's block to [10,13] (arrival = 10)
# 6: Salzburg   (4 days)
cities = ["Budapest", "Copenhagen", "Hamburg", "Vienna", "Reykjavik", "Split", "Salzburg"]
durations = [4, 2, 4, 5, 2, 4, 4]

# Total raw days = 4+2+4+5+2+4+4 = 25.
# There are 6 transitions (each transit day is counted only once),
# so overall trip duration = 25 - 6 = 19 days.

# Allowed direct flights (bidirectional):
#  1. Hamburg and Salzburg    -> {Hamburg (2), Salzburg (6)}
#  2. Copenhagen and Split     -> {Copenhagen (1), Split (5)}
#  3. Vienna and Copenhagen    -> {Vienna (3), Copenhagen (1)}
#  4. Vienna and Split         -> {Vienna (3), Split (5)}
#  5. Reykjavik and Copenhagen -> {Reykjavik (4), Copenhagen (1)}
#  6. Copenhagen and Hamburg   -> {Copenhagen (1), Hamburg (2)}
#  7. Budapest and Hamburg     -> {Budapest (0), Hamburg (2)}
#  8. Vienna and Hamburg       -> {Vienna (3), Hamburg (2)}
#  9. Budapest and Reykjavik   -> {Budapest (0), Reykjavik (4)}
# 10. Vienna and Reykjavik     -> {Vienna (3), Reykjavik (4)}
# 11. Vienna and Budapest      -> {Vienna (3), Budapest (0)}
# 12. Split and Hamburg        -> {Split (5), Hamburg (2)}
# 13. Budapest and Copenhagen   -> {Budapest (0), Copenhagen (1)}
direct_flights = [
    ("Hamburg", "Salzburg"),
    ("Copenhagen", "Split"),
    ("Vienna", "Copenhagen"),
    ("Vienna", "Split"),
    ("Reykjavik", "Copenhagen"),
    ("Copenhagen", "Hamburg"),
    ("Budapest", "Hamburg"),
    ("Vienna", "Hamburg"),
    ("Budapest", "Reykjavik"),
    ("Vienna", "Reykjavik"),
    ("Vienna", "Budapest"),
    ("Split", "Hamburg"),
    ("Budapest", "Copenhagen")
]

# Map city names to indices.
city_to_idx = { city: idx for idx, city in enumerate(cities) }

# Build allowed unordered flight pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({ city_to_idx[a], city_to_idx[b] }))

# Create Z3 solver.
s = Solver()
n = len(cities)

# Define the visitation order as a permutation of city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit slot.
# Each city visit has an arrival day and its departure is arrival + duration - 1.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit i, if the visited city is c then
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 19.
s.add(departures[n-1] == 19)

# Time-specific event constraints:
# Vienna (index 3): Conference during day 1 and day 5
for i in range(n):
    s.add(If(order[i] == city_to_idx["Vienna"],
             arrivals[i] == 1,  # then Vienna's block is [1,5]
             True))

# Reykjavik (index 4): Wedding between day 8 and day 9
for i in range(n):
    s.add(If(order[i] == city_to_idx["Reykjavik"],
             arrivals[i] == 8,  # then Reykjavik's block is [8,9]
             True))

# Split (index 5): Meeting friends between day 10 and day 13
for i in range(n):
    s.add(If(order[i] == city_to_idx["Split"],
             arrivals[i] == 10,  # then Split's block is [10,13]
             True))

# Connectivity constraints:
# Each consecutive pair of cities in the order must be connected by one allowed direct flight.
for i in range(n - 1):
    conn_options = []
    for pair in allowed_pairs:
        pair_list = list(pair)
        a, b = pair_list[0], pair_list[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(conn_options))

# Solve the model and output the itinerary.
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
        print(f"  {city:10s} : [{a}, {d}]")
else:
    print("No solution found")