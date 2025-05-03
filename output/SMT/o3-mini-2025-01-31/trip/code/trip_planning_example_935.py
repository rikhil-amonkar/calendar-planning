from z3 import *

# We have 7 cities with the following durations and event constraints:
# 0: Zurich   (3 days)
# 1: Split    (4 days)
# 2: Tallinn  (2 days) – Workshop in Tallinn between day 18 and day 19 → force arrival = 18 (block: [18,19])
# 3: Rome     (5 days) – Meet friends in Rome between day 5 and day 9 → force arrival = 5 (block: [5,9])
# 4: Vienna   (5 days) – Annual show in Vienna from day 1 to day 5 → force arrival = 1 (block: [1,5])
# 5: Nice     (3 days)
# 6: Brussels (3 days)
cities = ["Zurich", "Split", "Tallinn", "Rome", "Vienna", "Nice", "Brussels"]
durations = [3, 4, 2, 5, 5, 3, 3]

# Total raw days = 3 + 4 + 2 + 5 + 5 + 3 + 3 = 25.
# There are 6 transitions (each consecutive visit shares a day),
# so overall trip duration = 25 - 6 = 19 days.

# Allowed direct flights (bidirectional):
# 1. Zurich and Brussels         -> {Zurich, Brussels}       -> {0,6}
# 2. Vienna and Brussels         -> {Vienna, Brussels}       -> {4,6}
# 3. Split and Zurich            -> {Split, Zurich}          -> {1,0}
# 4. Vienna and Rome             -> {Vienna, Rome}           -> {4,3}
# 5. Rome and Brussels           -> {Rome, Brussels}         -> {3,6}
# 6. Vienna and Nice             -> {Vienna, Nice}           -> {4,5}
# 7. Zurich and Tallinn          -> {Zurich, Tallinn}        -> {0,2}
# 8. Zurich and Nice             -> {Zurich, Nice}           -> {0,5}
# 9. Vienna and Zurich           -> {Vienna, Zurich}         -> {4,0}
# 10. Rome and Zurich            -> {Rome, Zurich}           -> {3,0}
# 11. Rome and Nice              -> {Rome, Nice}             -> {3,5}
# 12. Vienna and Split           -> {Vienna, Split}          -> {4,1}
# 13. Brussels and Tallinn       -> {Brussels, Tallinn}      -> {6,2}
# 14. Rome and Split             -> {Rome, Split}            -> {3,1}
# 15. Nice and Brussels          -> {Nice, Brussels}         -> {5,6}
direct_flights = [
    ("Zurich", "Brussels"),
    ("Vienna", "Brussels"),
    ("Split", "Zurich"),
    ("Vienna", "Rome"),
    ("Rome", "Brussels"),
    ("Vienna", "Nice"),
    ("Zurich", "Tallinn"),
    ("Zurich", "Nice"),
    ("Vienna", "Zurich"),
    ("Rome", "Zurich"),
    ("Rome", "Nice"),
    ("Vienna", "Split"),
    ("Brussels", "Tallinn"),
    ("Rome", "Split"),
    ("Nice", "Brussels")
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

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the visited city is c then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day: the arrival of visit i+1 equals the departure of visit i.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 19.
s.add(departures[n-1] == 19)

# Time-specific event constraints:
# Vienna: Annual show from day 1 to 5 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Vienna"],
             arrivals[i] == 1,
             True))

# Rome: Meet friends from day 5 to 9 → force arrival = 5.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Rome"],
             arrivals[i] == 5,
             True))

# Tallinn: Workshop between day 18 and 19 → force arrival = 18.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Tallinn"],
             arrivals[i] == 18,
             True))

# Connectivity constraints:
# Each consecutive pair in the visitation order must be connected by a direct flight.
for i in range(n - 1):
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