from z3 import *

# City indices and durations:
# 0: Venice    (4 days) – Meet friends in Venice between day 6 and day 9, so force its block to be [6,9] → arrival == 6.
# 1: Florence  (4 days)
# 2: Brussels  (2 days) – Annual show in Brussels between day 5 and day 6, so force its block to be [5,6] → arrival == 5.
# 3: Dublin    (3 days)
# 4: Valencia  (2 days)
# 5: London    (4 days) – Wedding in London between day 9 and day 12, so force its block to be [9,12] → arrival == 9.
# 6: Stuttgart (2 days)
cities = ["Venice", "Florence", "Brussels", "Dublin", "Valencia", "London", "Stuttgart"]
durations = [4, 4, 2, 3, 2, 4, 2]

# Total raw days = 4 + 4 + 2 + 3 + 2 + 4 + 2 = 21.
# There are 6 transitions shared between cities, so overall trip duration = 21 - 6 = 15 days.

# Allowed direct flights (bidirectional):
# 1. London and Florence     -> {London, Florence}      -> {5, 1}
# 2. Brussels and Venice      -> {Brussels, Venice}       -> {2, 0}
# 3. Brussels and London      -> {Brussels, London}       -> {2, 5}
# 4. Valencia and London      -> {Valencia, London}       -> {4, 5}
# 5. Stuttgart and Venice     -> {Stuttgart, Venice}      -> {6, 0}
# 6. Brussels and Florence    -> {Brussels, Florence}     -> {2, 1}
# 7. Valencia and Brussels    -> {Valencia, Brussels}     -> {4, 2}
# 8. Valencia and Dublin      -> {Valencia, Dublin}       -> {4, 3}
# 9. Dublin and Venice        -> {Dublin, Venice}         -> {3, 0}
# 10. Stuttgart and Valencia   -> {Stuttgart, Valencia}    -> {6, 4}
# 11. Stuttgart and London     -> {Stuttgart, London}      -> {6, 5}
# 12. Venice and London        -> {Venice, London}         -> {0, 5}
# 13. Dublin and Brussels      -> {Dublin, Brussels}       -> {3, 2}
# 14. Dublin and London        -> {Dublin, London}         -> {3, 5}
direct_flights = [
    ("London", "Florence"),
    ("Brussels", "Venice"),
    ("Brussels", "London"),
    ("Valencia", "London"),
    ("Stuttgart", "Venice"),
    ("Brussels", "Florence"),
    ("Valencia", "Brussels"),
    ("Valencia", "Dublin"),
    ("Dublin", "Venice"),
    ("Stuttgart", "Valencia"),
    ("Stuttgart", "London"),
    ("Venice", "London"),
    ("Dublin", "Brussels"),
    ("Dublin", "London")
]

# Map city names to indices.
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Build the set of allowed unordered pairs.
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

# Define arrival and departure day for each visit slot.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each slot i, if the visited city is c then departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share a transit day: the next arrival equals the current departure.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 15.
s.add(departures[n-1] == 15)

# Event constraints:
# Venice (index 0): Meeting friends between day 6 and day 9
# Force Venice's stay to be [6,9]: arrival == 6.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Venice"],
             arrivals[i] == 6,
             True))
             
# Brussels (index 2): Annual show from day 5 to day 6
# Force Brussels's stay to be [5,6]: arrival == 5.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Brussels"],
             arrivals[i] == 5,
             True))

# London (index 5): Wedding between day 9 and day 12
# Force London's stay to be [9,12]: arrival == 9.
for i in range(n):
    s.add(If(order[i] == city_to_idx["London"],
             arrivals[i] == 9,
             True))

# Connectivity constraints:
# Every consecutive pair in the order must be connected by a direct flight.
for i in range(n - 1):
    conn_options = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(conn_options))

# Solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    # List itinerary in visitation order.
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        itinerary.append((cities[city_idx], a_day, d_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:10s} : [{a}, {d}]")
else:
    print("No solution found")