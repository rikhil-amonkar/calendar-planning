from z3 import *

# City indices and durations:
# 0: Vienna   (4 days) – Conference in Vienna: must cover day 1 and day 4, so Vienna's block is fixed to [1,4].
# 1: Milan    (2 days)
# 2: Rome     (3 days)
# 3: Riga     (2 days)
# 4: Lisbon   (3 days) – Relatives in Lisbon between day 11 and day 13, so Lisbon's block is fixed to [11,13].
# 5: Vilnius  (4 days)
# 6: Oslo     (3 days) – Meet a friend in Oslo between day 13 and day 15, so Oslo's block is fixed to [13,15].
cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
durations = [4, 2, 3, 2, 3, 4, 3]

# Total raw days = 4 + 2 + 3 + 2 + 3 + 4 + 3 = 21.
# There are 6 transitions (i.e. shared days for flights), so overall trip length = 21 - 6 = 15 days.

# Allowed direct flights (bidirectional):
# "Riga and Oslo"         -> {Riga, Oslo}            -> {3,6}
# "Rome and Oslo"         -> {Rome, Oslo}            -> {2,6}
# "Vienna and Milan"      -> {Vienna, Milan}         -> {0,1}
# "Vienna and Vilnius"    -> {Vienna, Vilnius}       -> {0,5}
# "Vienna and Lisbon"     -> {Vienna, Lisbon}        -> {0,4}
# "Riga and Milan"        -> {Riga, Milan}           -> {3,1}
# "Lisbon and Oslo"       -> {Lisbon, Oslo}          -> {4,6}
# "from Rome to Riga"     -> {Rome, Riga}            -> {2,3}  (treat bidirectionally)
# "Rome and Lisbon"       -> {Rome, Lisbon}          -> {2,4}
# "Vienna and Riga"       -> {Vienna, Riga}          -> {0,3}
# "Vienna and Rome"       -> {Vienna, Rome}          -> {0,2}
# "Milan and Oslo"        -> {Milan, Oslo}           -> {1,6}
# "Vienna and Oslo"       -> {Vienna, Oslo}          -> {0,6}
# "Vilnius and Oslo"      -> {Vilnius, Oslo}         -> {5,6}
# "from Riga to Vilnius"  -> {Riga, Vilnius}         -> {3,5}
# "Vilnius and Milan"     -> {Vilnius, Milan}        -> {5,1}
# "Riga and Lisbon"       -> {Riga, Lisbon}          -> {3,4}
# "Milan and Lisbon"      -> {Milan, Lisbon}         -> {1,4}
direct_flights = [
    ("Riga", "Oslo"),
    ("Rome", "Oslo"),
    ("Vienna", "Milan"),
    ("Vienna", "Vilnius"),
    ("Vienna", "Lisbon"),
    ("Riga", "Milan"),
    ("Lisbon", "Oslo"),
    ("Rome", "Riga"),
    ("Rome", "Lisbon"),
    ("Vienna", "Riga"),
    ("Vienna", "Rome"),
    ("Milan", "Oslo"),
    ("Vienna", "Oslo"),
    ("Vilnius", "Oslo"),
    ("Riga", "Vilnius"),
    ("Vilnius", "Milan"),
    ("Riga", "Lisbon"),
    ("Milan", "Lisbon")
]

# Map city names to indices.
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed unordered pairs.
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({ city_to_idx[a], city_to_idx[b] }))

# Create Z3 solver.
s = Solver()
n = len(cities)

# Define the order in which the cities are visited (a permutation of 0..6).
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the city visited is c then:
# departure = arrival + duration[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day:
# For i from 0 to n-2, arrivals[i+1] == departures[i].
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 15.
s.add(departures[n-1] == 15)

# Time-specific event constraints:
# 1. Vienna (index 0): Conference from day 1 to day 4,
#    so force Vienna's arrival to be 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Vienna"],
             arrivals[i] == 1,
             True))

# 2. Lisbon (index 4): Visit relatives in Lisbon between day 11 and day 13,
#    so force Lisbon's arrival to be 11 (block [11,13]).
for i in range(n):
    s.add(If(order[i] == city_to_idx["Lisbon"],
             arrivals[i] == 11,
             True))

# 3. Oslo (index 6): Meet a friend in Oslo between day 13 and day 15,
#    so force Oslo's arrival to be 13 (block [13,15]).
for i in range(n):
    s.add(If(order[i] == city_to_idx["Oslo"],
             arrivals[i] == 13,
             True))

# Connectivity constraints:
# Each consecutive pair of cities must be connected by a direct flight.
for i in range(n-1):
    possible = []
    for pair in allowed_pairs:
        pair_list = list(pair)
        a, b = pair_list[0], pair_list[1]
        possible.append(And(order[i] == a, order[i+1] == b))
        possible.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(possible))

# Solve the constraints and print the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        start_day = m.evaluate(arrivals[i]).as_long()
        end_day = m.evaluate(departures[i]).as_long()
        itinerary.append((cities[city_idx], start_day, end_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:8s}: [{a}, {d}]")
else:
    print("No solution found")