from z3 import *

# Define the 7 cities with their durations and event constraints:
# 0: Milan      (2 days) – Conference between day 13 and 14 ⇒ force arrival = 13.
# 1: Valencia   (3 days)
# 2: Frankfurt  (2 days)
# 3: Santorini  (3 days) – Meet friends between day 11 and 13 ⇒ force arrival = 11.
# 4: Mykonos    (3 days)
# 5: Manchester (5 days)
# 6: Rome       (4 days) – Workshop between day 1 and 4 ⇒ force arrival = 1.
cities = ["Milan", "Valencia", "Frankfurt", "Santorini", "Mykonos", "Manchester", "Rome"]
durations = [2, 3, 2, 3, 3, 5, 4]

# Total raw days = 2 + 3 + 2 + 3 + 3 + 5 + 4 = 22 days.
# There are 6 transitions (consecutive visits share one day),
# therefore overall trip length = 22 - 6 = 16 days.

# Allowed direct flights (bidirectional):
# 1. Manchester and Milan      -> {Manchester, Milan}       -> {5, 0}
# 2. Santorini and Milan       -> {Santorini, Milan}        -> {3, 0}
# 3. Rome and Frankfurt        -> {Rome, Frankfurt}         -> {6, 2}
# 4. Rome and Manchester       -> {Rome, Manchester}        -> {6, 5}
# 5. Frankfurt and Milan       -> {Frankfurt, Milan}        -> {2, 0}
# 6. Valencia and Frankfurt    -> {Valencia, Frankfurt}     -> {1, 2}
# 7. Rome and Valencia         -> {Rome, Valencia}          -> {6, 1}
# 8. Rome and Santorini        -> {Rome, Santorini}         -> {6, 3}
# 9. Frankfurt and Manchester  -> {Frankfurt, Manchester}   -> {2, 5}
# 10. Milan and Mykonos        -> {Milan, Mykonos}          -> {0, 4}
# 11. Rome and Mykonos         -> {Rome, Mykonos}           -> {6, 4}
# 12. Manchester and Santorini -> {Manchester, Santorini}   -> {5, 3}
# 13. Valencia and Milan       -> {Valencia, Milan}         -> {1, 0}
direct_flights = [
    ("Manchester", "Milan"),
    ("Santorini", "Milan"),
    ("Rome", "Frankfurt"),
    ("Rome", "Manchester"),
    ("Frankfurt", "Milan"),
    ("Valencia", "Frankfurt"),
    ("Rome", "Valencia"),
    ("Rome", "Santorini"),
    ("Frankfurt", "Manchester"),
    ("Milan", "Mykonos"),
    ("Rome", "Mykonos"),
    ("Manchester", "Santorini"),
    ("Valencia", "Milan")
]

# Map city names to indices.
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Build allowed flight connections as unordered pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define a permutation for the visitation order.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit slot.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the visited city is c then:
#    departures[i] = arrivals[i] + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share a transit day: arrival[i+1] equals departures[i].
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 16.
s.add(departures[n-1] == 16)

# Time-specific event constraints:
# Rome workshop: force arrival of Rome (city index 6) = 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Rome"], arrivals[i] == 1, True))
# Milan conference: force arrival of Milan (city index 0) = 13.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Milan"], arrivals[i] == 13, True))
# Santorini friends meet: force arrival of Santorini (city index 3) = 11.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Santorini"], arrivals[i] == 11, True))

# Connectivity constraints:
# For each consecutive pair of visits, the two cities must have a direct flight between them.
for i in range(n - 1):
    flight_options = []
    for pair in allowed_pairs:
        pair_list = list(pair)
        a, b = pair_list[0], pair_list[1]
        flight_options.append(And(order[i] == a, order[i+1] == b))
        flight_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(*flight_options))

# Find and print the solution.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:11s}: [{a_day}, {d_day}]")
else:
    print("No solution found")