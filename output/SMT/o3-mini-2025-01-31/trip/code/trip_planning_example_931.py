from z3 import *

# City indices and durations:
# 0: Seville    (2 days) – Wedding in Seville between day 10 and day 11 → force arrival = 10 (block: [10,11])
# 1: Milan      (2 days)
# 2: London     (3 days)
# 3: Paris      (3 days) – Workshop in Paris between day 11 and day 13 → force arrival = 11 (block: [11,13])
# 4: Oslo       (5 days) – Annual show in Oslo from day 13 to day 17 → force arrival = 13 (block: [13,17])
# 5: Copenhagen (3 days)
# 6: Tallinn    (5 days)
cities = ["Seville", "Milan", "London", "Paris", "Oslo", "Copenhagen", "Tallinn"]
durations = [2, 2, 3, 3, 5, 3, 5]

# Total raw days = 2 + 2 + 3 + 3 + 5 + 3 + 5 = 23.
# With 6 transitions shared between consecutive visits, overall trip duration = 23 - 6 = 17 days.

# Allowed direct flights (bidirectional):
# 1. London and Paris
# 2. Seville and Paris
# 3. Copenhagen and Milan
# 4. Milan and Oslo
# 5. Copenhagen and London
# 6. Milan and Paris
# 7. Tallinn and Copenhagen
# 8. London and Oslo
# 9. Copenhagen and Paris
# 10. Tallinn and Oslo
# 11. Paris and Oslo
# 12. Tallinn and Paris
# 13. Copenhagen and Oslo
# 14. London and Milan
# 15. Milan and Seville
direct_flights = [
    ("London", "Paris"),
    ("Seville", "Paris"),
    ("Copenhagen", "Milan"),
    ("Milan", "Oslo"),
    ("Copenhagen", "London"),
    ("Milan", "Paris"),
    ("Tallinn", "Copenhagen"),
    ("London", "Oslo"),
    ("Copenhagen", "Paris"),
    ("Tallinn", "Oslo"),
    ("Paris", "Oslo"),
    ("Tallinn", "Paris"),
    ("Copenhagen", "Oslo"),
    ("London", "Milan"),
    ("Milan", "Seville")
]

# Map city names to indices.
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Build allowed unordered flight pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the visitation order as a permutation of city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(*order))

# Define arrival and departure day variables per visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the visited city is c then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 17.
s.add(departures[n-1] == 17)

# Time-specific event constraints:
# Seville: Wedding between day 10 and day 11 → force arrival = 10.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Seville"],
             arrivals[i] == 10,
             True))
# Paris: Workshop between day 11 and day 13 → force arrival = 11.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Paris"],
             arrivals[i] == 11,
             True))
# Oslo: Annual show from day 13 to day 17 → force arrival = 13.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Oslo"],
             arrivals[i] == 13,
             True))

# Connectivity constraints:
# Each consecutive pair of cities in the visitation order must be connected by a direct flight.
for i in range(n - 1):
    conn_options = []
    for pair in allowed_pairs:
        pair_list = list(pair)
        a, b = pair_list[0], pair_list[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(*conn_options))

# Solve the model and print the itinerary.
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
        print(f"  {city:12s}: [{a}, {d}]")
else:
    print("No solution found")