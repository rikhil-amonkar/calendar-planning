from z3 import *

# City indices and durations:
# 0: Split     (3 days)
# 1: Bucharest (2 days)
# 2: Copenhagen (3 days)
# 3: Stockholm  (2 days)
# 4: Hamburg    (3 days) – Annual show from day 10 to day 12, so force Hamburg block: [10,12] (arrival = 10)
# 5: Porto      (4 days) – Conference from day 7 to day 10, so force Porto block: [7,10] (arrival = 7)
# 6: Istanbul   (2 days) – Meet friends between day 4 and day 5, so force Istanbul block: [4,5] (arrival = 4)
cities = ["Split", "Bucharest", "Copenhagen", "Stockholm", "Hamburg", "Porto", "Istanbul"]
durations = [3, 2, 3, 2, 3, 4, 2]

# Total raw days = 3 + 2 + 3 + 2 + 3 + 4 + 2 = 19.
# There are 6 transitions (shared days between consecutive visits), so overall trip duration = 19 - 6 = 13 days.

# Allowed direct flights (bidirectional):
# 1. Stockholm and Istanbul    -> {Stockholm, Istanbul}          -> {3, 6}
# 2. Copenhagen and Porto       -> {Copenhagen, Porto}            -> {2, 5}
# 3. Stockholm and Hamburg      -> {Stockholm, Hamburg}           -> {3, 4}
# 4. Split and Copenhagen       -> {Split, Copenhagen}            -> {0, 2}
# 5. Split and Hamburg          -> {Split, Hamburg}               -> {0, 4}
# 6. Istanbul and Hamburg       -> {Istanbul, Hamburg}            -> {6, 4}
# 7. Istanbul and Porto         -> {Istanbul, Porto}              -> {6, 5}
# 8. Istanbul and Copenhagen    -> {Istanbul, Copenhagen}         -> {6, 2}
# 9. Copenhagen and Hamburg     -> {Copenhagen, Hamburg}          -> {2, 4}
# 10. Istanbul and Bucharest    -> {Istanbul, Bucharest}          -> {6, 1}
# 11. Split and Stockholm       -> {Split, Stockholm}             -> {0, 3}
# 12. Stockholm and Copenhagen  -> {Stockholm, Copenhagen}        -> {3, 2}
# 13. Porto and Hamburg         -> {Porto, Hamburg}               -> {5, 4}
# 14. Copenhagen and Bucharest  -> {Copenhagen, Bucharest}        -> {2, 1}
# 15. Hamburg and Bucharest     -> {Hamburg, Bucharest}           -> {4, 1}
direct_flights = [
    ("Stockholm", "Istanbul"),
    ("Copenhagen", "Porto"),
    ("Stockholm", "Hamburg"),
    ("Split", "Copenhagen"),
    ("Split", "Hamburg"),
    ("Istanbul", "Hamburg"),
    ("Istanbul", "Porto"),
    ("Istanbul", "Copenhagen"),
    ("Copenhagen", "Hamburg"),
    ("Istanbul", "Bucharest"),
    ("Split", "Stockholm"),
    ("Stockholm", "Copenhagen"),
    ("Porto", "Hamburg"),
    ("Copenhagen", "Bucharest"),
    ("Hamburg", "Bucharest")
]

# Map city names to indices.
city_to_idx = { city: idx for idx, city in enumerate(cities) }

# Build allowed unordered flight pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Create the Z3 solver.
s = Solver()
n = len(cities)

# Define the visitation order as a permutation of the cities.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit slot.
# Departure is computed as: departure = arrival + duration - 1.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For every visit i, if the visit is city c then:
# departures[i] = arrivals[i] + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day (departure of one equals arrival of the next).
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 13.
s.add(departures[n-1] == 13)

# Time-specific event constraints:
# Hamburg (index 4): Annual show from day 10 to day 12, force arrival = 10.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Hamburg"],
             arrivals[i] == 10,
             True))

# Porto (index 5): Conference from day 7 to day 10, force arrival = 7.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Porto"],
             arrivals[i] == 7,
             True))

# Istanbul (index 6): Meet friends between day 4 and day 5, force arrival = 4.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Istanbul"],
             arrivals[i] == 4,
             True))

# Connectivity constraints:
# Each consecutive pair of cities in the visit order must be connected by a direct flight.
for i in range(n - 1):
    conn_options = []
    for pair in allowed_pairs:
        pair_list = list(pair)
        a, b = pair_list[0], pair_list[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(conn_options))

# Solve the model and output the itinerary.
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
        print(f"  {city:12s} : [{a}, {d}]")
else:
    print("No solution found")