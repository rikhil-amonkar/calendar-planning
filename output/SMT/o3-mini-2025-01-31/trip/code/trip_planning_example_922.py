from z3 import *

# City indices and durations:
# 0: Amsterdam  (2 days) – Visit relatives in Amsterdam between day 6 and day 7, so Amsterdam block = [6,7]
# 1: Brussels   (5 days)
# 2: Milan      (5 days)
# 3: Reykjavik  (4 days)
# 4: Frankfurt  (2 days) – Attend a workshop in Frankfurt between day 5 and day 6, so Frankfurt block = [5,6]
# 5: Split      (2 days) – Wedding in Split between day 14 and day 15, so Split block = [14,15]
# 6: Hamburg    (4 days)
cities = ["Amsterdam", "Brussels", "Milan", "Reykjavik", "Frankfurt", "Split", "Hamburg"]
durations = [2, 5, 5, 4, 2, 2, 4]

# Total raw days = 2 + 5 + 5 + 4 + 2 + 2 + 4 = 24.
# With 6 transitions (shared flight days) overall trip duration = 24 - 6 = 18 days.

# Allowed direct flights (bidirectional):
# 1. Reykjavik and Milan           -> {Reykjavik, Milan}         -> {3, 2}
# 2. Frankfurt and Amsterdam       -> {Frankfurt, Amsterdam}     -> {4, 0}
# 3. Frankfurt and Reykjavik       -> {Frankfurt, Reykjavik}     -> {4, 3}
# 4. Amsterdam and Milan           -> {Amsterdam, Milan}         -> {0, 2}
# 5. Amsterdam and Split           -> {Amsterdam, Split}         -> {0, 5}
# 6. Frankfurt and Milan           -> {Frankfurt, Milan}         -> {4, 2}
# 7. Amsterdam and Hamburg         -> {Amsterdam, Hamburg}       -> {0, 6}
# 8. Frankfurt and Hamburg         -> {Frankfurt, Hamburg}       -> {4, 6}
# 9. Frankfurt and Split           -> {Frankfurt, Split}         -> {4, 5}
# 10. from Brussels to Frankfurt   -> {Brussels, Frankfurt}      -> {1, 4}
# 11. Split and Hamburg            -> {Split, Hamburg}           -> {5, 6}
# 12. Brussels and Reykjavik       -> {Brussels, Reykjavik}      -> {1, 3}
# 13. Milan and Hamburg            -> {Milan, Hamburg}           -> {2, 6}
# 14. Brussels and Hamburg         -> {Brussels, Hamburg}        -> {1, 6}
# 15. Milan and Split              -> {Milan, Split}             -> {2, 5}
# 16. Amsterdam and Reykjavik      -> {Amsterdam, Reykjavik}     -> {0, 3}
# 17. Brussels and Milan           -> {Brussels, Milan}          -> {1, 2}
direct_flights = [
    ("Reykjavik", "Milan"),
    ("Frankfurt", "Amsterdam"),
    ("Frankfurt", "Reykjavik"),
    ("Amsterdam", "Milan"),
    ("Amsterdam", "Split"),
    ("Frankfurt", "Milan"),
    ("Amsterdam", "Hamburg"),
    ("Frankfurt", "Hamburg"),
    ("Frankfurt", "Split"),
    ("Brussels", "Frankfurt"),
    ("Split", "Hamburg"),
    ("Brussels", "Reykjavik"),
    ("Milan", "Hamburg"),
    ("Brussels", "Hamburg"),
    ("Milan", "Split"),
    ("Amsterdam", "Reykjavik"),
    ("Brussels", "Milan")
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

# Define order: a permutation of cities indices representing the visitation order.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit slot.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the visited city is c then: departure = arrival + duration[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the flight (transit) day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 18.
s.add(departures[n-1] == 18)

# Event constraints:
# Amsterdam (index 0): Relatives between day 6 and day 7 -> force Amsterdam block to [6,7]
for i in range(n):
    s.add(If(order[i] == city_to_idx["Amsterdam"],
             arrivals[i] == 6,
             True))
             
# Frankfurt (index 4): Workshop between day 5 and day 6 -> force Frankfurt block to [5,6]
for i in range(n):
    s.add(If(order[i] == city_to_idx["Frankfurt"],
             arrivals[i] == 5,
             True))

# Split (index 5): Wedding between day 14 and day 15 -> force Split block to [14,15]
for i in range(n):
    s.add(If(order[i] == city_to_idx["Split"],
             arrivals[i] == 14,
             True))

# Connectivity constraints:
# Each consecutive pair of cities must be connected by one of the allowed direct flights.
for i in range(n - 1):
    connections = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        connections.append(And(order[i] == a, order[i+1] == b))
        connections.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(connections))

# Solve the constraints and print the solution itinerary.
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