from z3 import *

# Define the 7 cities, their durations, and any event-related arrival constraints.
# We'll index the cities as follows:
# 0: Amsterdam  (4 days)
# 1: Stuttgart  (2 days) – Conference during day 4 & 5, so force arrival = 4.
# 2: Bucharest  (4 days)
# 3: Brussels   (3 days) – Friends meet between day 10 and 12, so force arrival = 10.
# 4: Tallinn   (3 days) – Annual show from day 8 to 10, so force arrival = 8.
# 5: Milan     (2 days)
# 6: Seville   (3 days)

cities = ["Amsterdam", "Stuttgart", "Bucharest", "Brussels", "Tallinn", "Milan", "Seville"]
durations = [4, 2, 4, 3, 3, 2, 3]

# Total raw days = 4+2+4+3+3+2+3 = 21 days.
# Since there are 6 transitions (each consecutive visit shares one day),
# the overall trip length = 21 - 6 = 15 days.

# Allowed direct flights (bidirectional):
# 1. Seville and Brussels    -> {Seville, Brussels}    -> {6, 3}
# 2. Brussels and Bucharest   -> {Brussels, Bucharest}  -> {3, 2}
# 3. Seville and Milan        -> {Seville, Milan}       -> {6, 5}
# 4. Amsterdam and Tallinn    -> {Amsterdam, Tallinn}   -> {0, 4}
# 5. Seville and Amsterdam    -> {Seville, Amsterdam}   -> {6, 0}
# 6. Milan and Amsterdam      -> {Milan, Amsterdam}     -> {5, 0}
# 7. Milan and Brussels       -> {Milan, Brussels}      -> {5, 3}
# 8. Tallinn and Brussels     -> {Tallinn, Brussels}    -> {4, 3}
# 9. Stuttgart and Amsterdam  -> {Stuttgart, Amsterdam} -> {1, 0}
# 10. Milan and Stuttgart     -> {Milan, Stuttgart}     -> {5, 1}
# 11. Amsterdam and Bucharest -> {Amsterdam, Bucharest} -> {0, 2}
direct_flights = [
    ("Seville", "Brussels"),
    ("Brussels", "Bucharest"),
    ("Seville", "Milan"),
    ("Amsterdam", "Tallinn"),
    ("Seville", "Amsterdam"),
    ("Milan", "Amsterdam"),
    ("Milan", "Brussels"),
    ("Tallinn", "Brussels"),
    ("Stuttgart", "Amsterdam"),
    ("Milan", "Stuttgart"),
    ("Amsterdam", "Bucharest")
]

# Map city names to indices.
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Build allowed flight connections as unordered pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Set up Z3 solver.
s = Solver()
n = len(cities)  # Number of cities is 7

# Define visitation order as a permutation of the city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, assign departure based on city's duration:
#    departure = arrival + duration - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share one day (arrival of visit i+1 is the same as departure of visit i).
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall, the trip must finish on day 15.
s.add(departures[n-1] == 15)

# Time-specific event constraints:
# Stuttgart (city 1): conference on day 4-5, so force arrival = 4.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Stuttgart"], arrivals[i] == 4, True))
# Brussels (city 3): meet friends between day 10 and 12, so force arrival = 10.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Brussels"], arrivals[i] == 10, True))
# Tallinn (city 4): annual show from day 8 to 10, so force arrival = 8.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Tallinn"], arrivals[i] == 8, True))

# Connectivity constraints:
# Consecutive cities in the itinerary must have a direct flight connection.
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
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:12s}: [{a_day}, {d_day}]")
else:
    print("No solution found")