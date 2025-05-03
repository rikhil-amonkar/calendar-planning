from z3 import *

# There are 7 cities with the following durations and event constraints:
# 0: Zurich    (2 days)
# 1: Seville   (3 days) – Wedding in Seville between day 5 and day 7, so force arrival = 5 (block: [5,7])
# 2: Naples    (5 days)
# 3: Hamburg   (2 days)
# 4: Amsterdam (4 days)
# 5: Porto     (4 days)
# 6: Venice    (2 days) – Meet friends in Venice between day 1 and day 2, so force arrival = 1 (block: [1,2])
cities = ["Zurich", "Seville", "Naples", "Hamburg", "Amsterdam", "Porto", "Venice"]
durations = [2, 3, 5, 2, 4, 4, 2]

# Total raw days = 2 + 3 + 5 + 2 + 4 + 4 + 2 = 22.
# There are 6 transitions, so overall trip duration = 22 - 6 = 16 days.

# Allowed direct flights (bidirectional):
# 1. Venice and Naples         -> {Venice, Naples} -> {6, 2}
# 2. Porto and Zurich           -> {Porto, Zurich} -> {5, 0}
# 3. Seville and Porto          -> {Seville, Porto} -> {1, 5}
# 4. Hamburg and Zurich         -> {Hamburg, Zurich} -> {3, 0}
# 5. Venice and Zurich          -> {Venice, Zurich} -> {6, 0}
# 6. Amsterdam and Hamburg      -> {Amsterdam, Hamburg} -> {4, 3}
# 7. Amsterdam and Porto        -> {Amsterdam, Porto} -> {4, 5}
# 8. Venice and Amsterdam       -> {Venice, Amsterdam} -> {6, 4}
# 9. Zurich and Naples          -> {Zurich, Naples} -> {0, 2}
# 10. Amsterdam and Seville     -> {Amsterdam, Seville} -> {4, 1}
# 11. Porto and Hamburg         -> {Porto, Hamburg} -> {5, 3}
# 12. Amsterdam and Naples      -> {Amsterdam, Naples} -> {4, 2}
# 13. Amsterdam and Zurich      -> {Amsterdam, Zurich} -> {4, 0}
# 14. Venice and Hamburg        -> {Venice, Hamburg} -> {6, 3}
direct_flights = [
    ("Venice", "Naples"),
    ("Porto", "Zurich"),
    ("Seville", "Porto"),
    ("Hamburg", "Zurich"),
    ("Venice", "Zurich"),
    ("Amsterdam", "Hamburg"),
    ("Amsterdam", "Porto"),
    ("Venice", "Amsterdam"),
    ("Zurich", "Naples"),
    ("Amsterdam", "Seville"),
    ("Porto", "Hamburg"),
    ("Amsterdam", "Naples"),
    ("Amsterdam", "Zurich"),
    ("Venice", "Hamburg")
]

# Map city names to indices.
city_to_idx = { city: idx for idx, city in enumerate(cities) }

# Build set of allowed unordered flight pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))
    
# Set up the Z3 solver.
s = Solver()
n = len(cities)

# Define the visitation order as a permutation of the city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit slot.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit i, if the visited city is c then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 16.
s.add(departures[n-1] == 16)

# Time-specific event constraints:
# Seville (city 1): wedding between day 5 and 7 → force arrival = 5.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Seville"],
             arrivals[i] == 5,
             True))

# Venice (city 6): meet friends between day 1 and 2 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Venice"],
             arrivals[i] == 1,
             True))
    
# Connectivity constraints:
# Every consecutive pair of cities in the order must be connected by a direct flight.
for i in range(n - 1):
    conn_options = []
    for pair in allowed_pairs:
        pair_list = list(pair)
        a, b = pair_list[0], pair_list[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(*conn_options))

# Solve the constraints and output the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_idx = m[order[i]].as_long()
        arr_day = m[arrivals[i]].as_long()
        dep_day = m[departures[i]].as_long()
        itinerary.append((cities[city_idx], arr_day, dep_day))
    for city, a, d in itinerary:
        print(f"  {city:10s} : [{a}, {d}]")
else:
    print("No solution found")