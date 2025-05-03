from z3 import *

# Cities and their durations:
# 0: Istanbul   (4 days)
# 1: Amsterdam  (4 days) – Wedding in Amsterdam between day 1 and day 4 → block [1,4]
# 2: Stuttgart  (5 days)
# 3: Vienna     (2 days)
# 4: Mykonos    (4 days)
# 5: Barcelona  (2 days) – Annual show in Barcelona between day 4 and day 5 → block [4,5]
# 6: Geneva     (3 days) – Meet friends in Geneva between day 8 and day 10 → block [8,10]
cities = ["Istanbul", "Amsterdam", "Stuttgart", "Vienna", "Mykonos", "Barcelona", "Geneva"]
durations = [4, 4, 5, 2, 4, 2, 3]

# Total raw days = 4 + 4 + 5 + 2 + 4 + 2 + 3 = 24.
# There are 6 transitions (shared flight days), so overall trip duration = 24 - 6 = 18 days.

# Allowed direct flights (bidirectional):
# 1. Barcelona and Vienna      -> {Barcelona, Vienna}       -> {5, 3}
# 2. Amsterdam and Barcelona   -> {Amsterdam, Barcelona}    -> {1, 5}
# 3. Vienna and Stuttgart      -> {Vienna, Stuttgart}       -> {3, 2}
# 4. Istanbul and Geneva       -> {Istanbul, Geneva}        -> {0, 6}
# 5. Istanbul and Vienna       -> {Istanbul, Vienna}        -> {0, 3}
# 6. Istanbul and Stuttgart    -> {Istanbul, Stuttgart}     -> {0, 2}
# 7. Barcelona and Stuttgart   -> {Barcelona, Stuttgart}    -> {5, 2}
# 8. Amsterdam and Mykonos     -> {Amsterdam, Mykonos}      -> {1, 4}
# 9. Barcelona and Geneva      -> {Barcelona, Geneva}       -> {5, 6}
# 10. Amsterdam and Istanbul   -> {Amsterdam, Istanbul}     -> {1, 0}
# 11. Amsterdam and Stuttgart  -> {Amsterdam, Stuttgart}    -> {1, 2}
# 12. Amsterdam and Geneva     -> {Amsterdam, Geneva}       -> {1, 6}
# 13. Barcelona and Istanbul   -> {Barcelona, Istanbul}     -> {5, 0}
# 14. Amsterdam and Vienna     -> {Amsterdam, Vienna}       -> {1, 3}
# 15. Geneva and Mykonos       -> {Geneva, Mykonos}         -> {6, 4}
# 16. Mykonos and Vienna       -> {Mykonos, Vienna}         -> {4, 3}
# 17. Geneva and Vienna        -> {Geneva, Vienna}          -> {6, 3}
direct_flights = [
    ("Barcelona", "Vienna"),
    ("Amsterdam", "Barcelona"),
    ("Vienna", "Stuttgart"),
    ("Istanbul", "Geneva"),
    ("Istanbul", "Vienna"),
    ("Istanbul", "Stuttgart"),
    ("Barcelona", "Stuttgart"),
    ("Amsterdam", "Mykonos"),
    ("Barcelona", "Geneva"),
    ("Amsterdam", "Istanbul"),
    ("Amsterdam", "Stuttgart"),
    ("Amsterdam", "Geneva"),
    ("Barcelona", "Istanbul"),
    ("Amsterdam", "Vienna"),
    ("Geneva", "Mykonos"),
    ("Mykonos", "Vienna"),
    ("Geneva", "Vienna")
]

# Map cities to indices.
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed unordered pairs for connectivity.
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({ city_to_idx[a], city_to_idx[b] }))

s = Solver()
n = len(cities)

# Define order: a permutation of the cities indices indicating the visitation order.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define variables for arrival (arr) and departure (dep) days for each visit slot.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the visited city is c then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, 
                   departures[i] == arrivals[i] + durations[c] - 1, 
                   False)
              for c in range(n)]))

# Consecutive visits share the transit (flight) day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 18.
s.add(departures[n-1] == 18)

# Time-specific event constraints:
# Amsterdam (index 1): Wedding between day 1 and day 4, so force Amsterdam block to [1,4] → arrival == 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Amsterdam"],
             arrivals[i] == 1,
             True))
             
# Barcelona (index 5): Annual show between day 4 and day 5, so force Barcelona block to [4,5] → arrival == 4.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Barcelona"],
             arrivals[i] == 4,
             True))
             
# Geneva (index 6): Meet friends between day 8 and day 10, so force Geneva block to [8,10] → arrival == 8.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Geneva"],
             arrivals[i] == 8,
             True))

# Connectivity constraints: 
# Each consecutive pair of visited cities must be connected by a direct flight.
for i in range(n - 1):
    connection_options = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        connection_options.append(And(order[i] == a, order[i+1] == b))
        connection_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(connection_options))

# Solve
if s.check() == sat:
    m = s.model()
    itinerary = []
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