from z3 import *

# Define the 7 cities with their durations and event constraints:
# 0: Krakow   (5 days) – Meet friends in Krakow between day 1 and 5 → force arrival = 1.
# 1: Paris    (2 days)
# 2: Riga     (3 days)
# 3: Seville  (3 days)
# 4: Mykonos  (2 days) – Wedding in Mykonos between day 9 and 10 → force arrival = 9.
# 5: Nice     (2 days)
# 6: Vienna   (5 days)
cities = ["Krakow", "Paris", "Riga", "Seville", "Mykonos", "Nice", "Vienna"]
durations = [5, 2, 3, 3, 2, 2, 5]

# Total raw days = 5+2+3+3+2+2+5 = 22.
# There are 6 transitions (each consecutive visit shares one day) so the overall trip length is 22 - 6 = 16 days.

# Allowed direct flights (bidirectional):
# 1. Krakow and Vienna     -> {Krakow, Vienna}       -> {0,6}
# 2. Paris and Seville       -> {Paris, Seville}         -> {1,3}
# 3. Mykonos and Nice        -> {Mykonos, Nice}          -> {4,5}
# 4. Vienna and Riga         -> {Vienna, Riga}           -> {6,2}
# 5. Vienna and Nice         -> {Vienna, Nice}           -> {6,5}
# 6. Nice and Riga           -> {Nice, Riga}             -> {5,2}
# 7. Riga and Paris          -> {Riga, Paris}            -> {2,1}
# 8. Krakow and Paris        -> {Krakow, Paris}          -> {0,1}
# 9. Vienna and Mykonos      -> {Vienna, Mykonos}        -> {6,4}
# 10. Vienna and Paris       -> {Vienna, Paris}          -> {6,1}
# 11. Nice and Paris         -> {Nice, Paris}            -> {5,1}
# 12. Vienna and Seville     -> {Vienna, Seville}        -> {6,3}
direct_flights = [
    ("Krakow", "Vienna"),
    ("Paris", "Seville"),
    ("Mykonos", "Nice"),
    ("Vienna", "Riga"),
    ("Vienna", "Nice"),
    ("Nice", "Riga"),
    ("Riga", "Paris"),
    ("Krakow", "Paris"),
    ("Vienna", "Mykonos"),
    ("Vienna", "Paris"),
    ("Nice", "Paris"),
    ("Vienna", "Seville")
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

# Define the visitation order as a permutation of the city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, the departure day is determined by the city's duration.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share a transit day:
# arrival of visit i+1 equals departure of visit i.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 16.
s.add(departures[n-1] == 16)

# Time-specific event constraints:
# For Krakow, meet friends between day 1 and day 5 -> force arrival = 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Krakow"], arrivals[i] == 1, True))
# For Mykonos, wedding between day 9 and day 10 -> force arrival = 9.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Mykonos"], arrivals[i] == 9, True))

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

# Solve and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:8s}: [{a_day}, {d_day}]")
else:
    print("No solution found")