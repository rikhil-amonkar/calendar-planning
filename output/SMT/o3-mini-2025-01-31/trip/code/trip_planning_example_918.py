from z3 import *

# City indices and durations:
# 0: Lyon      (3 days) – Meet friends in Lyon between day 8 and day 10.
# 1: Lisbon    (4 days)
# 2: Reykjavik (4 days)
# 3: Manchester(5 days)
# 4: Bucharest (2 days)
# 5: Oslo      (3 days) – Visit relatives in Oslo between day 15 and day 17.
# 6: Nice      (5 days) – Attend a workshop in Nice between day 1 and day 5.
cities = ["Lyon", "Lisbon", "Reykjavik", "Manchester", "Bucharest", "Oslo", "Nice"]
durations = [3, 4, 4, 5, 2, 3, 5]

# Total raw days = 3+4+4+5+2+3+5 = 26.
# There are 6 transitions (shared flight days) so overall trip = 26 - 6 = 20 days.

# Allowed direct flights (bidirectional):
# 1. Lisbon and Manchester      -> {Lisbon, Manchester}       -> {1, 3}
# 2. Nice and Lyon              -> {Nice, Lyon}               -> {6, 0}
# 3. Bucharest and Oslo         -> {Bucharest, Oslo}          -> {4, 5}
# 4. Nice and Lisbon            -> {Nice, Lisbon}             -> {6, 1}
# 5. Manchester and Oslo        -> {Manchester, Oslo}         -> {3, 5}
# 6. Oslo and Reykjavik         -> {Oslo, Reykjavik}          -> {5, 2}
# 7. Nice and Manchester        -> {Nice, Manchester}         -> {6, 3}
# 8. Lyon and Oslo              -> {Lyon, Oslo}               -> {0, 5}
# 9. Bucharest and Manchester   -> {Bucharest, Manchester}    -> {4, 3}
# 10. Lyon and Bucharest        -> {Lyon, Bucharest}          -> {0, 4}
# 11. Lisbon and Oslo           -> {Lisbon, Oslo}             -> {1, 5}
# 12. Nice and Oslo             -> {Nice, Oslo}               -> {6, 5}
# 13. Lisbon and Lyon           -> {Lisbon, Lyon}             -> {1, 0}
# 14. Nice and Reykjavik        -> {Nice, Reykjavik}          -> {6, 2}
# 15. Lisbon and Reykjavik      -> {Lisbon, Reykjavik}        -> {1, 2}
# 16. Lisbon and Bucharest      -> {Lisbon, Bucharest}        -> {1, 4}
direct_flights = [
    ("Lisbon", "Manchester"),
    ("Nice", "Lyon"),
    ("Bucharest", "Oslo"),
    ("Nice", "Lisbon"),
    ("Manchester", "Oslo"),
    ("Oslo", "Reykjavik"),
    ("Nice", "Manchester"),
    ("Lyon", "Oslo"),
    ("Bucharest", "Manchester"),
    ("Lyon", "Bucharest"),
    ("Lisbon", "Oslo"),
    ("Nice", "Oslo"),
    ("Lisbon", "Lyon"),
    ("Nice", "Reykjavik"),
    ("Lisbon", "Reykjavik"),
    ("Lisbon", "Bucharest")
]

# Map city names to indices.
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed unordered pairs from the direct flights.
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({ city_to_idx[a], city_to_idx[b] }))

s = Solver()
n = len(cities)

# Define the order (permutation) in which cities are visited.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if we visit city c then departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the flight (transit) day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 20.
s.add(departures[n-1] == 20)

# Time-specific event constraints:
# Nice (index 6): Workshop in Nice between day 1 and day 5.
# For a 5-day stay, we fix the block to cover that window by forcing arrival = 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Nice"],
             arrivals[i] == 1,
             True))

# Lyon (index 0): Meet friends in Lyon between day 8 and day 10.
# With a 3-day stay, to cover that window we can fix the block to [8,10] by forcing arrival = 8.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Lyon"],
             arrivals[i] == 8,
             True))

# Oslo (index 5): Visit relatives in Oslo between day 15 and day 17.
# With a 3-day stay, fix the block to [15,17] by forcing arrival = 15.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Oslo"],
             arrivals[i] == 15,
             True))

# Connectivity constraints:
# Each consecutive pair of cities must be connected by one of the allowed direct flights.
for i in range(n - 1):
    options = []
    for pair in allowed_pairs:
        pair_list = list(pair)
        # Unpack the two cities from the pair.
        a, b = pair_list[0], pair_list[1]
        options.append(And(order[i] == a, order[i+1] == b))
        options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(options))

# Solve the constraints and print the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        start = m.evaluate(arrivals[i]).as_long()
        end = m.evaluate(departures[i]).as_long()
        itinerary.append((cities[city_idx], start, end))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:12s}: [{a}, {d}]")
else:
    print("No solution found")