from z3 import *

# City indices and durations:
# 0: Zurich   (5 days)
# 1: Venice   (2 days) – Meet friend between day 2 and day 3 (Venice visit should cover that interval).
# 2: Berlin   (2 days) – Wedding between day 1 and day 2 (Berlin visit should cover that interval).
# 3: Split    (5 days) – Annual show between day 13 and day 17 (Split visit must cover that period).
# 4: Rome     (2 days)
# 5: Riga     (2 days)
# 6: Krakow   (5 days)
cities = ["Zurich", "Venice", "Berlin", "Split", "Rome", "Riga", "Krakow"]
durations = [5, 2, 2, 5, 2, 2, 5]

# Total raw days = 5+2+2+5+2+2+5 = 23.
# There are 6 transitions (shared flight days) so overall trip length = 23 - 6 = 17 days.

# Allowed direct flights (bidirectional):
# - Berlin and Venice         -> {Berlin,Venice}        -> {2, 1}
# - Venice and Rome           -> {Venice,Rome}          -> {1, 4}
# - Zurich and Split          -> {Zurich,Split}         -> {0, 3}
# - Rome and Zurich           -> {Rome,Zurich}          -> {4, 0}
# - Zurich and Krakow         -> {Zurich,Krakow}        -> {0, 6}
# - Venice and Zurich         -> {Venice,Zurich}        -> {1, 0}
# - Berlin and Krakow         -> {Berlin,Krakow}        -> {2, 6}
# - Riga and Zurich           -> {Riga,Zurich}          -> {5, 0}
# - Berlin and Split          -> {Berlin,Split}         -> {2, 3}
# - Berlin and Rome           -> {Berlin,Rome}          -> {2, 4}
# - Berlin and Zurich         -> {Berlin,Zurich}        -> {2, 0}
# - Rome and Split            -> {Rome,Split}           -> {4, 3}
# - from Rome to Riga         -> {Rome,Riga}            -> {4, 5} (bidirectional)
# - Berlin and Riga           -> {Berlin,Riga}          -> {2, 5}
# - Krakow and Split          -> {Krakow,Split}         -> {6, 3}
direct_flights = [
    ("Berlin", "Venice"),
    ("Venice", "Rome"),
    ("Zurich", "Split"),
    ("Rome", "Zurich"),
    ("Zurich", "Krakow"),
    ("Venice", "Zurich"),
    ("Berlin", "Krakow"),
    ("Riga", "Zurich"),
    ("Berlin", "Split"),
    ("Berlin", "Rome"),
    ("Berlin", "Zurich"),
    ("Rome", "Split"),
    ("Rome", "Riga"),
    ("Berlin", "Riga"),
    ("Krakow", "Split")
]

# Map city names to indices.
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed unordered pairs.
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({ city_to_idx[a], city_to_idx[b] }))

# Create the Z3 solver instance.
s = Solver()
n = len(cities)

# Define the order in which cities are visited as a permutation of  {0,...,6}.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit slot.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the city is c then departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit (flight) day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 17.
s.add(departures[n-1] == 17)

# Time-specific constraints:
# 1. Berlin (index 2): Wedding between day 1 and day 2.
#    Berlin's 2-day block is [a, a+1]. To cover a wedding between day1 and day2, force a == 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Berlin"],
             arrivals[i] == 1,
             True))

# 2. Venice (index 1): Meet friend between day 2 and day 3.
#    Venice's block is [a, a+1]. To cover the interval [2,3], force a == 2.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Venice"],
             arrivals[i] == 2,
             True))

# 3. Split (index 3): Annual show between day 13 and day 17.
#    Split's block is [a, a+4]. To fully cover days 13 to 17, we force a == 13.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Split"],
             arrivals[i] == 13,
             True))

# Connectivity constraints:
# Consecutive cities in the itinerary must have a direct flight between them.
for i in range(n - 1):
    conn_options = []
    for pair in allowed_pairs:
        a, b = list(pair)
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(conn_options))

# Solve the constraints and print the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_index = m.eval(order[i]).as_long()
        arr_day = m.eval(arrivals[i]).as_long()
        dep_day = m.eval(departures[i]).as_long()
        itinerary.append((cities[city_index], arr_day, dep_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:8s} [{a}, {d}]")
else:
    print("No solution found")