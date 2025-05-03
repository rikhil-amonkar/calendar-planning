from z3 import *

# City indices and durations:
# 0: Split    (2 days) – Conference in Split during day 16 and day 17 → force arrival = 16 (block: [16,17])
# 1: Oslo     (4 days) – Annual show in Oslo from day 3 to day 6 → force arrival = 3 (block: [3,6])
# 2: Tallinn  (3 days)
# 3: Hamburg  (2 days)
# 4: Vilnius  (5 days)
# 5: Dublin   (3 days) – Visit relatives in Dublin between day 1 and day 3 → force arrival = 1 (block: [1,3])
# 6: Vienna   (4 days)
cities = ["Split", "Oslo", "Tallinn", "Hamburg", "Vilnius", "Dublin", "Vienna"]
durations = [2, 4, 3, 2, 5, 3, 4]

# Compute total raw days: 2+4+3+2+5+3+4 = 23.
# There are 6 transitions (shared days between visits), so overall trip duration = 23 - 6 = 17 days.

# Allowed direct flights (bidirectional):
# 1. Dublin and Hamburg      -> (Dublin, Hamburg)       -> (5, 3)
# 2. Dublin and Vienna       -> (Dublin, Vienna)        -> (5, 6)
# 3. Dublin and Tallinn      -> (Dublin, Tallinn)       -> (5, 2)
# 4. Oslo and Vienna         -> (Oslo, Vienna)          -> (1, 6)
# 5. Vilnius and Split       -> (Vilnius, Split)        -> (4, 0)
# 6. Vilnius and Vienna      -> (Vilnius, Vienna)       -> (4, 6)
# 7. Hamburg and Split       -> (Hamburg, Split)        -> (3, 0)
# 8. Oslo and Vilnius        -> (Oslo, Vilnius)         -> (1, 4)
# 9. Dublin and Oslo         -> (Dublin, Oslo)          -> (5, 1)
# 10. Dublin and Split       -> (Dublin, Split)         -> (5, 0)
# 11. Oslo and Split         -> (Oslo, Split)           -> (1, 0)
# 12. Vienna and Split       -> (Vienna, Split)         -> (6, 0)
# 13. Oslo and Hamburg       -> (Oslo, Hamburg)         -> (1, 3)
# 14. Vienna and Hamburg     -> (Vienna, Hamburg)       -> (6, 3)
# 15. from Tallinn to Vilnius -> (Tallinn, Vilnius)      -> (2, 4)
# 16. Oslo and Tallinn       -> (Oslo, Tallinn)         -> (1, 2)
direct_flights = [
    ("Dublin", "Hamburg"),
    ("Dublin", "Vienna"),
    ("Dublin", "Tallinn"),
    ("Oslo", "Vienna"),
    ("Vilnius", "Split"),
    ("Vilnius", "Vienna"),
    ("Hamburg", "Split"),
    ("Oslo", "Vilnius"),
    ("Dublin", "Oslo"),
    ("Dublin", "Split"),
    ("Oslo", "Split"),
    ("Vienna", "Split"),
    ("Oslo", "Hamburg"),
    ("Vienna", "Hamburg"),
    ("Tallinn", "Vilnius"),
    ("Oslo", "Tallinn")
]

# Map city names to indices.
city_to_idx = {city: idx for idx, city in enumerate(cities)}

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

# Define the arrival and departure day variables.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the visited city is c then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 17.
s.add(departures[n-1] == 17)

# Time-specific event constraints:
# Dublin (city 5): relatives between day 1 and day 3 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Dublin"],
             arrivals[i] == 1,
             True))

# Oslo (city 1): annual show from day 3 to day 6 → force arrival = 3.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Oslo"],
             arrivals[i] == 3,
             True))

# Split (city 0): conference during day 16 and 17 → force arrival = 16.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Split"],
             arrivals[i] == 16,
             True))

# Connectivity constraints:
# Each consecutive pair in the order must be connected via a direct flight.
for i in range(n - 1):
    conn_options = []
    for pair in allowed_pairs:
        # For each unordered pair, generate disjunctive constraints
        pair_list = list(pair)
        a, b = pair_list[0], pair_list[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(*conn_options))

# Solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_idx = m[order[i]].as_long()
        arr_day = m[arrivals[i]].as_long()
        dep_day = m[departures[i]].as_long()
        itinerary.append((cities[city_idx], arr_day, dep_day))
    for city, a, d in itinerary:
        print(f"  {city:8s}: [{a}, {d}]")
else:
    print("No solution found")