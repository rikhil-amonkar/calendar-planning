from z3 import *

# City indices and durations:
# 0: Oslo       (3 days) – Meet a friend in Oslo between day 12 and day 14 → force Oslo’s block to [12,14] (arrival == 12)
# 1: Lisbon     (5 days)
# 2: Milan      (3 days) – Annual show in Milan from day 14 to day 16 → force Milan’s block to [14,16] (arrival == 14)
# 3: Salzburg   (4 days)
# 4: Brussels   (2 days)
# 5: Mykonos    (5 days) – Conference in Mykonos during day 16 to day 20 → force Mykonos’ block to [16,20] (arrival == 16)
# 6: Frankfurt  (4 days)
cities = ["Oslo", "Lisbon", "Milan", "Salzburg", "Brussels", "Mykonos", "Frankfurt"]
durations = [3, 5, 3, 4, 2, 5, 4]

# Total raw days = 3 + 5 + 3 + 4 + 2 + 5 + 4 = 26.
# There are 6 transitions (each transit day is shared between consecutive visits),
# so overall trip duration = 26 - 6 = 20 days.

# Allowed direct flights (bidirectional):
# 1. Lisbon and Oslo         -> {Lisbon, Oslo}              -> {1, 0}
# 2. Lisbon and Brussels     -> {Lisbon, Brussels}          -> {1, 4}
# 3. Brussels and Frankfurt  -> {Brussels, Frankfurt}       -> {4, 6}   (from Brussels to Frankfurt is given; treat as bidirectional)
# 4. Frankfurt and Milan     -> {Frankfurt, Milan}          -> {6, 2}
# 5. Brussels and Oslo       -> {Brussels, Oslo}            -> {4, 0}
# 6. Brussels and Milan      -> {Brussels, Milan}           -> {4, 2}
# 7. Lisbon and Milan        -> {Lisbon, Milan}             -> {1, 2}
# 8. Oslo and Milan          -> {Oslo, Milan}               -> {0, 2}
# 9. Frankfurt and Oslo       -> {Frankfurt, Oslo}           -> {6, 0}
# 10. Salzburg and Frankfurt  -> {Salzburg, Frankfurt}       -> {3, 6}
# 11. Milan and Mykonos       -> {Milan, Mykonos}            -> {2, 5}
# 12. Frankfurt and Lisbon    -> {Frankfurt, Lisbon}         -> {6, 1}
direct_flights = [
    ("Lisbon", "Oslo"),
    ("Lisbon", "Brussels"),
    ("Brussels", "Frankfurt"),
    ("Frankfurt", "Milan"),
    ("Brussels", "Oslo"),
    ("Brussels", "Milan"),
    ("Lisbon", "Milan"),
    ("Oslo", "Milan"),
    ("Frankfurt", "Oslo"),
    ("Salzburg", "Frankfurt"),
    ("Milan", "Mykonos"),
    ("Frankfurt", "Lisbon"),
]

# Map city names to indices.
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed unordered pairs for connectivity.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Create the Z3 solver.
s = Solver()
n = len(cities)

# Define the visitation order as a permutation of city indices.
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
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit (flight) day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 20.
s.add(departures[n-1] == 20)

# Time-specific event constraints:
# Oslo (index 0): Meeting a friend between day 12 and day 14 → force Oslo’s block to [12,14] (arrival == 12)
for i in range(n):
    s.add(If(order[i] == city_to_idx["Oslo"],
             arrivals[i] == 12,
             True))

# Milan (index 2): Annual show from day 14 to day 16 → force Milan’s block to [14,16] (arrival == 14)
for i in range(n):
    s.add(If(order[i] == city_to_idx["Milan"],
             arrivals[i] == 14,
             True))

# Mykonos (index 5): Conference from day 16 to day 20 → force Mykonos’ block to [16,20] (arrival == 16)
for i in range(n):
    s.add(If(order[i] == city_to_idx["Mykonos"],
             arrivals[i] == 16,
             True))

# Connectivity constraints:
# Each consecutive pair of cities in the visitation order must be connected by an allowed direct flight.
for i in range(n - 1):
    conn_options = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(conn_options))

# Solve the constraints and output the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        itinerary.append((cities[city_idx], arr_day, dep_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:10s} : [{a}, {d}]")
else:
    print("No solution found")