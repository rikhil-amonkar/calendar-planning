from z3 import *

# Define the 7 cities with their durations and event constraints:
# 0: Lisbon    (2 days)
# 1: Venice    (2 days) – Annual show from day 12 to day 13 forces arrival = 12.
# 2: Dubrovnik (4 days)
# 3: Edinburgh (5 days)
# 4: Vienna    (2 days)
# 5: Seville   (3 days)
# 6: Munich    (5 days) – Meet a friend between day 13 and day 17 forces arrival = 13.
cities = ["Lisbon", "Venice", "Dubrovnik", "Edinburgh", "Vienna", "Seville", "Munich"]
durations = [2, 2, 4, 5, 2, 3, 5]

# Total raw days = 2+2+4+5+2+3+5 = 23.
# There are 6 transitions (each consecutive visit shares one day) so the total trip length is 23 - 6 = 17 days.

# Allowed direct flights (bidirectional):
# 1. Lisbon and Munich        -> (Lisbon, Munich)               -> (0,6)
# 2. Vienna and Munich        -> (Vienna, Munich)               -> (4,6)
# 3. Dubrovnik and Munich     -> (Dubrovnik, Munich)            -> (2,6)
# 4. Edinburgh and Venice     -> (Edinburgh, Venice)            -> (3,1)
# 5. Vienna and Lisbon        -> (Vienna, Lisbon)               -> (4,0)
# 6. Seville and Munich       -> (Seville, Munich)              -> (5,6)
# 7. Vienna and Seville       -> (Vienna, Seville)              -> (4,5)
# 8. Seville and Edinburgh    -> (Seville, Edinburgh)           -> (5,3)
# 9. Venice and Munich        -> (Venice, Munich)               -> (1,6)
# 10. Edinburgh and Munich    -> (Edinburgh, Munich)            -> (3,6)
# 11. Dubrovnik and Vienna    -> (Dubrovnik, Vienna)            -> (2,4)
# 12. Vienna and Venice       -> (Vienna, Venice)               -> (4,1)
# 13. Lisbon and Seville      -> (Lisbon, Seville)              -> (0,5)
# 14. Lisbon and Venice       -> (Lisbon, Venice)               -> (0,1)
direct_flights = [
    ("Lisbon", "Munich"),
    ("Vienna", "Munich"),
    ("Dubrovnik", "Munich"),
    ("Edinburgh", "Venice"),
    ("Vienna", "Lisbon"),
    ("Seville", "Munich"),
    ("Vienna", "Seville"),
    ("Seville", "Edinburgh"),
    ("Venice", "Munich"),
    ("Edinburgh", "Munich"),
    ("Dubrovnik", "Vienna"),
    ("Vienna", "Venice"),
    ("Lisbon", "Seville"),
    ("Lisbon", "Venice")
]

# Map city names to indices.
city_to_idx = { city: idx for idx, city in enumerate(cities) }

# Build allowed flight connections as unordered pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define visitation order as a permutation of city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the visited city is c then:
#   departures[i] = arrivals[i] + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day:
# arrival of visit i+1 equals departure of visit i.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 17.
s.add(departures[n-1] == 17)

# Time-specific event constraints:
# Venice (city 1): Annual show from day 12 to 13 → force arrival = 12.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Venice"],
             arrivals[i] == 12,
             True))
# Munich (city 6): Friend meeting between day 13 and day 17 → force arrival = 13.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Munich"],
             arrivals[i] == 13,
             True))

# Connectivity constraints:
# Each consecutive pair must be connected by a direct flight.
for i in range(n-1):
    flight_options = []
    for pair in allowed_pairs:
        pair_list = list(pair)
        a, b = pair_list[0], pair_list[1]
        flight_options.append(And(order[i] == a, order[i+1] == b))
        flight_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(*flight_options))

# Solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:10s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")