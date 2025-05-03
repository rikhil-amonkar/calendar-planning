from z3 import *

# City indices and durations:
# 0: Stuttgart  (2 days) – Annual show from day 6 to day 7 → force Stuttgart block to [6,7] (arrival = 6)
# 1: Frankfurt  (4 days)
# 2: Riga       (3 days)
# 3: Krakow     (4 days)
# 4: Brussels   (2 days)
# 5: Istanbul   (5 days) – Wedding between day 13 and day 17 → force Istanbul block to [13,17] (arrival = 13)
# 6: Tallinn    (3 days)
cities = ["Stuttgart", "Frankfurt", "Riga", "Krakow", "Brussels", "Istanbul", "Tallinn"]
durations = [2, 4, 3, 4, 2, 5, 3]

# Total raw days = 2 + 4 + 3 + 4 + 2 + 5 + 3 = 23.
# There are 6 transitions (each transit day shared between consecutive visits),
# so overall trip duration = 23 - 6 = 17 days.

# Allowed direct flights (bidirectional, treating "from" as directional hint but solving bidirectionally):
# 1. Krakow and Istanbul         -> (Krakow, Istanbul)         -> (3, 5)
# 2. from Istanbul to Tallinn      -> (Istanbul, Tallinn)        -> (5, 6)
# 3. from Riga to Tallinn          -> (Riga, Tallinn)            -> (2, 6)
# 4. Frankfurt and Stuttgart       -> (Frankfurt, Stuttgart)     -> (1, 0)
# 5. Stuttgart and Istanbul        -> (Stuttgart, Istanbul)      -> (0, 5)
# 6. Tallinn and Brussels          -> (Tallinn, Brussels)        -> (6, 4)
# 7. Stuttgart and Krakow          -> (Stuttgart, Krakow)        -> (0, 3)
# 8. Brussels and Istanbul         -> (Brussels, Istanbul)       -> (4, 5)
# 9. Brussels and Riga             -> (Brussels, Riga)           -> (4, 2)
# 10. Frankfurt and Riga           -> (Frankfurt, Riga)          -> (1, 2)
# 11. Tallinn and Frankfurt        -> (Tallinn, Frankfurt)       -> (6, 1)
# 12. Krakow and Brussels          -> (Krakow, Brussels)         -> (3, 4)
# 13. from Brussels to Frankfurt   -> (Brussels, Frankfurt)      -> (4, 1)
# 14. Frankfurt and Istanbul       -> (Frankfurt, Istanbul)      -> (1, 5)
# 15. Frankfurt and Krakow         -> (Frankfurt, Krakow)        -> (1, 3)
# 16. Riga and Istanbul            -> (Riga, Istanbul)           -> (2, 5)
direct_flights = [
    ("Krakow", "Istanbul"),
    ("Istanbul", "Tallinn"),
    ("Riga", "Tallinn"),
    ("Frankfurt", "Stuttgart"),
    ("Stuttgart", "Istanbul"),
    ("Tallinn", "Brussels"),
    ("Stuttgart", "Krakow"),
    ("Brussels", "Istanbul"),
    ("Brussels", "Riga"),
    ("Frankfurt", "Riga"),
    ("Tallinn", "Frankfurt"),
    ("Krakow", "Brussels"),
    ("Brussels", "Frankfurt"),
    ("Frankfurt", "Istanbul"),
    ("Frankfurt", "Krakow"),
    ("Riga", "Istanbul")
]

# Map city names to indices.
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Build allowed unordered flight pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Create the Z3 solver.
s = Solver()
n = len(cities)

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

# For each visit i, if the visited city is c then departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 17.
s.add(departures[n-1] == 17)

# Time-specific event constraints:
# Stuttgart (index 0): Annual show from day 6 to day 7 → force Stuttgart block's arrival = 6.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Stuttgart"],
             arrivals[i] == 6,
             True))

# Istanbul (index 5): Wedding between day 13 and day 17 → force Istanbul block's arrival = 13.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Istanbul"],
             arrivals[i] == 13,
             True))

# Connectivity constraints:
# Each consecutive pair of cities in the visitation order must be connected by an allowed direct flight.
for i in range(n - 1):
    conn_options = []
    for pair in allowed_pairs:
        pair_list = list(pair)
        a, b = pair_list[0], pair_list[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(conn_options))

# Solve and output the itinerary.
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
        print(f"  {city:10s} : [{a}, {d}]")
else:
    print("No solution found")