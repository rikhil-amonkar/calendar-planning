from z3 import *

# City indices and durations:
# 0: Venice    (2 days)
# 1: Dubrovnik (3 days) – Visit relatives in Dubrovnik between day 17 and day 19, so block must be [17,19].
# 2: Valencia  (4 days) – Attend a conference in Valencia between day 8 and day 11, so block must be [8,11].
# 3: Bucharest (5 days)
# 4: Munich    (3 days)
# 5: Lisbon   (4 days)
# 6: Brussels  (4 days) – Meet a friend in Brussels between day 1 and day 4, so block must be [1,4].
cities = ["Venice", "Dubrovnik", "Valencia", "Bucharest", "Munich", "Lisbon", "Brussels"]
durations = [2, 3, 4, 5, 3, 4, 4]

# Total raw days = 2 + 3 + 4 + 5 + 3 + 4 + 4 = 25.
# There are 6 transitions shared between cities, so overall trip duration = 25 - 6 = 19 days.

# Allowed direct flights (bidirectional):
# "Valencia and Bucharest"   -> (Valencia, Bucharest)   -> (2, 3)
# "Brussels and Venice"      -> (Brussels, Venice)      -> (6, 0)
# "Bucharest and Munich"     -> (Bucharest, Munich)     -> (3, 4)
# "Venice and Munich"        -> (Venice, Munich)        -> (0, 4)
# "Valencia and Munich"      -> (Valencia, Munich)      -> (2, 4)
# "Venice and Lisbon"        -> (Venice, Lisbon)        -> (0, 5)
# "Lisbon and Valencia"      -> (Lisbon, Valencia)      -> (5, 2)
# "Brussels and Munich"      -> (Brussels, Munich)      -> (6, 4)
# "Brussels and Lisbon"      -> (Brussels, Lisbon)      -> (6, 5)
# "Brussels and Bucharest"   -> (Brussels, Bucharest)   -> (6, 3)
# "Lisbon and Munich"        -> (Lisbon, Munich)        -> (5, 4)
# "Munich and Dubrovnik"     -> (Munich, Dubrovnik)     -> (4, 1)
# "Brussels and Valencia"    -> (Brussels, Valencia)    -> (6, 2)
# "Lisbon and Bucharest"     -> (Lisbon, Bucharest)     -> (5, 3)
direct_flights = [
    ("Valencia", "Bucharest"),
    ("Brussels", "Venice"),
    ("Bucharest", "Munich"),
    ("Venice", "Munich"),
    ("Valencia", "Munich"),
    ("Venice", "Lisbon"),
    ("Lisbon", "Valencia"),
    ("Brussels", "Munich"),
    ("Brussels", "Lisbon"),
    ("Brussels", "Bucharest"),
    ("Lisbon", "Munich"),
    ("Munich", "Dubrovnik"),
    ("Brussels", "Valencia"),
    ("Lisbon", "Bucharest")
]

# Map city names to indices.
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed unordered pairs.
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({ city_to_idx[a], city_to_idx[b] }))

# Create the Z3 solver.
s = Solver()
n = len(cities)

# Define a permutation "order" for the visitation order.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival (arr) and departure (dep) day variables for each city visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip begins on day 1.
s.add(arrivals[0] == 1)

# Enforce that if city c is visited in the i-th slot, then departure = arrival + duration[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the flight (transit) day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 19.
s.add(departures[n-1] == 19)

# Time-specific event constraints:
# Brussels (index 6): Meet a friend between day 1 and day 4.
# For a 4-day stay, force Brussels's block to be [1,4] by setting arrival==1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Brussels"],
             arrivals[i] == 1,
             True))

# Valencia (index 2): Conference between day 8 and day 11.
# Force Valencia's block to be [8,11] by setting arrival==8.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Valencia"],
             arrivals[i] == 8,
             True))

# Dubrovnik (index 1): Relatives visit between day 17 and day 19.
# For a 3-day stay, force Dubrovnik's block to be [17,19] by setting arrival==17.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Dubrovnik"],
             arrivals[i] == 17,
             True))

# Connectivity constraints:
# Each consecutive pair of cities must be connected with an allowed direct flight.
for i in range(n - 1):
    conn_options = []
    for pair in allowed_pairs:
        lst = list(pair)
        # There are exactly two distinct cities in the pair.
        a, b = lst[0], lst[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(conn_options))

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
        print(f"  {city:10s} : [{a}, {d}]")
else:
    print("No solution found")