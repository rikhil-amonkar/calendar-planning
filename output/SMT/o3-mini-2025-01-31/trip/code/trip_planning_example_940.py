from z3 import *

# Define the 7 cities with their durations and any event-driven arrival constraints:
# 0: Athens    (5 days) – Wedding in Athens between day 1 and day 5 → force arrival = 1.
# 1: Frankfurt (4 days) – Workshop in Frankfurt between day 19 and day 22 → force arrival = 19.
# 2: Stuttgart (5 days) – Meet a friend in Stuttgart between day 13 and day 17 → force arrival = 13.
# 3: Helsinki  (3 days)
# 4: Naples    (5 days)
# 5: Valencia  (3 days)
# 6: Geneva    (3 days)
cities = ["Athens", "Frankfurt", "Stuttgart", "Helsinki", "Naples", "Valencia", "Geneva"]
durations = [5, 4, 5, 3, 5, 3, 3]

# Calculation of total trip days:
# Sum of durations = 5+4+5+3+5+3+3 = 28 days.
# There are 6 transitions (each consecutive visit shares one day) so total trip length = 28 - 6 = 22 days.

# Allowed direct flights (bidirectional), with cities given as indices:
# 1. Helsinki and Frankfurt         -> {Helsinki, Frankfurt}       -> {3, 1}
# 2. Athens and Stuttgart           -> {Athens, Stuttgart}         -> {0, 2}
# 3. Valencia and Frankfurt         -> {Valencia, Frankfurt}       -> {5, 1}
# 4. Geneva and Valencia            -> {Geneva, Valencia}          -> {6, 5}
# 5. Helsinki and Naples            -> {Helsinki, Naples}          -> {3, 4}
# 6. Geneva and Helsinki            -> {Geneva, Helsinki}          -> {6, 3}
# 7. from Valencia to Athens        -> {Valencia, Athens}          -> {5, 0}
# 8. Naples and Stuttgart           -> {Naples, Stuttgart}         -> {4, 2}
# 9. Stuttgart and Frankfurt        -> {Stuttgart, Frankfurt}      -> {2, 1}
# 10. Geneva and Frankfurt          -> {Geneva, Frankfurt}         -> {6, 1}
# 11. Naples and Valencia           -> {Naples, Valencia}          -> {4, 5}
# 12. Athens and Naples             -> {Athens, Naples}            -> {0, 4}
# 13. Stuttgart and Valencia        -> {Stuttgart, Valencia}       -> {2, 5}
# 14. Athens and Geneva             -> {Athens, Geneva}            -> {0, 6}
# 15. Athens and Frankfurt          -> {Athens, Frankfurt}         -> {0, 1}
# 16. Geneva and Naples             -> {Geneva, Naples}            -> {6, 4}
# 17. Naples and Frankfurt          -> {Naples, Frankfurt}         -> {4, 1}
direct_flights = [
    ("Helsinki", "Frankfurt"),
    ("Athens", "Stuttgart"),
    ("Valencia", "Frankfurt"),
    ("Geneva", "Valencia"),
    ("Helsinki", "Naples"),
    ("Geneva", "Helsinki"),
    ("Valencia", "Athens"),
    ("Naples", "Stuttgart"),
    ("Stuttgart", "Frankfurt"),
    ("Geneva", "Frankfurt"),
    ("Naples", "Valencia"),
    ("Athens", "Naples"),
    ("Stuttgart", "Valencia"),
    ("Athens", "Geneva"),
    ("Athens", "Frankfurt"),
    ("Geneva", "Naples"),
    ("Naples", "Frankfurt")
]

# Map city names to indices.
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Build the allowed flight connections as unordered pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({ city_to_idx[a], city_to_idx[b] }))

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

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

# For each visit slot i, if the visited city is 'c', then:
#   departure[i] = arrivals[i] + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share a transit day: for all i, arrivals[i+1] == departures[i].
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 22.
s.add(departures[n-1] == 22)

# Time-specific event constraints:
# Athens (city 0): Wedding between day 1 and day 5 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Athens"], arrivals[i] == 1, True))

# Frankfurt (city 1): Workshop between day 19 and day 22 → force arrival = 19.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Frankfurt"], arrivals[i] == 19, True))

# Stuttgart (city 2): Meet a friend between day 13 and day 17 → force arrival = 13.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Stuttgart"], arrivals[i] == 13, True))

# Connectivity constraints:
# Each consecutive pair in the itinerary must be connected by a direct flight.
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
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:12s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")