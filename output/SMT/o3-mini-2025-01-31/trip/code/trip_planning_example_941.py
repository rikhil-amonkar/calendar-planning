from z3 import *

# Define the 7 cities with their durations and any event-driven arrival constraints:
# 0: Valencia   (3 days)
# 1: Bucharest  (4 days)
# 2: Dubrovnik  (4 days)
# 3: Split      (3 days) – Annual show from day 1 to day 3 ⇒ force arrival = 1.
# 4: Amsterdam  (2 days)
# 5: Prague     (3 days)
# 6: Seville    (2 days)
cities = ["Valencia", "Bucharest", "Dubrovnik", "Split", "Amsterdam", "Prague", "Seville"]
durations = [3, 4, 4, 3, 2, 3, 2]

# Total raw days = 3 + 4 + 4 + 3 + 2 + 3 + 2 = 21.
# With 6 transitions (each consecutive pair sharing one day),
# overall trip duration = 21 - 6 = 15 days.

# Allowed direct flights (bidirectional):
# 1. Valencia and Amsterdam   -> {Valencia, Amsterdam}      -> {0, 4}
# 2. Seville and Amsterdam    -> {Seville, Amsterdam}       -> {6, 4}
# 3. Split and Amsterdam      -> {Split, Amsterdam}         -> {3, 4}
# 4. Amsterdam and Dubrovnik  -> {Amsterdam, Dubrovnik}     -> {4, 2}
# 5. Prague and Amsterdam     -> {Prague, Amsterdam}        -> {5, 4}
# 6. Split and Prague         -> {Split, Prague}            -> {3, 5}
# 7. Prague and Valencia      -> {Prague, Valencia}         -> {5, 0}
# 8. Bucharest and Amsterdam  -> {Bucharest, Amsterdam}     -> {1, 4}
# 9. Valencia and Seville     -> {Valencia, Seville}        -> {0, 6}
# 10. Prague and Bucharest    -> {Prague, Bucharest}        -> {5, 1}
# 11. Bucharest and Valencia  -> {Bucharest, Valencia}      -> {1, 0}
direct_flights = [
    ("Valencia", "Amsterdam"),
    ("Seville", "Amsterdam"),
    ("Split", "Amsterdam"),
    ("Amsterdam", "Dubrovnik"),
    ("Prague", "Amsterdam"),
    ("Split", "Prague"),
    ("Prague", "Valencia"),
    ("Bucharest", "Amsterdam"),
    ("Valencia", "Seville"),
    ("Prague", "Bucharest"),
    ("Bucharest", "Valencia")
]

# Map city names to indices.
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Build allowed flight connections as unordered pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({ city_to_idx[a], city_to_idx[b] }))

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

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the visited city is c then:
#   departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day:
# arrival of visit i+1 equals departure of visit i.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 15.
s.add(departures[n-1] == 15)

# Time-specific event constraint:
# Split (city 3) has an annual show from day 1 to day 3 ⇒ force arrival = 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Split"], arrivals[i] == 1, True))

# Connectivity constraints:
# Each consecutive pair of cities visited must be connected by a direct flight.
for i in range(n - 1):
    flight_options = []
    for pair in allowed_pairs:
        # Unpack the unordered pair.
        pair_list = list(pair)
        a, b = pair_list[0], pair_list[1]
        flight_options.append(And(order[i] == a, order[i+1] == b))
        flight_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(*flight_options))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:10s}: [{a_day}, {d_day}]")
else:
    print("No solution found")