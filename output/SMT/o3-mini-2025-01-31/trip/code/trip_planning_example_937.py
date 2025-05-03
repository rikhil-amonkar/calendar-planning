from z3 import *

# Define the cities, durations, and event constraints:
# 0: Dubrovnik  (2 days)
# 1: Bucharest   (3 days) – Meet friends between day 19 and day 21 → force arrival = 19
# 2: Santorini  (5 days)
# 3: Porto      (3 days) – Wedding between day 5 and day 7 → force arrival = 5
# 4: Stockholm  (5 days)
# 5: Istanbul   (5 days)
# 6: Frankfurt  (4 days)
cities = ["Dubrovnik", "Bucharest", "Santorini", "Porto", "Stockholm", "Istanbul", "Frankfurt"]
durations = [2, 3, 5, 3, 5, 5, 4]

# Total raw days = 2+3+5+3+5+5+4 = 27 days.
# With 6 transitions (each consecutive visit shares one day), the overall trip length is 27 - 6 = 21 days.

# Allowed direct flights (bidirectional):
# 1. Istanbul and Bucharest       -> (Istanbul, Bucharest)        -> (5, 1)
# 2. Istanbul and Stockholm       -> (Istanbul, Stockholm)        -> (5, 4)
# 3. Istanbul and Porto           -> (Istanbul, Porto)            -> (5, 3)
# 4. Stockholm and Santorini      -> (Stockholm, Santorini)       -> (4, 2)
# 5. Frankfurt and Stockholm      -> (Frankfurt, Stockholm)       -> (6, 4)
# 6. Frankfurt and Bucharest      -> (Frankfurt, Bucharest)       -> (6, 1)
# 7. Santorini and Bucharest      -> (Santorini, Bucharest)       -> (2, 1)
# 8. Istanbul and Frankfurt       -> (Istanbul, Frankfurt)        -> (5, 6)
# 9. Dubrovnik and Stockholm      -> (Dubrovnik, Stockholm)       -> (0, 4)
# 10. Frankfurt and Dubrovnik     -> (Frankfurt, Dubrovnik)       -> (6, 0)
# 11. Porto and Frankfurt         -> (Porto, Frankfurt)           -> (3, 6)
# 12. Dubrovnik and Istanbul      -> (Dubrovnik, Istanbul)        -> (0, 5)
direct_flights = [
    ("Istanbul", "Bucharest"),
    ("Istanbul", "Stockholm"),
    ("Istanbul", "Porto"),
    ("Stockholm", "Santorini"),
    ("Frankfurt", "Stockholm"),
    ("Frankfurt", "Bucharest"),
    ("Santorini", "Bucharest"),
    ("Istanbul", "Frankfurt"),
    ("Dubrovnik", "Stockholm"),
    ("Frankfurt", "Dubrovnik"),
    ("Porto", "Frankfurt"),
    ("Dubrovnik", "Istanbul")
]

# Map city names to indices.
city_to_idx = { city: idx for idx, city in enumerate(cities) }

# Build set of allowed flight connections (unordered pairs).
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # should be 7

# Define the visitation order as a permutation of the city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the visited city is c then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day:
# arrival of visit i+1 equals departure of visit i.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 21.
s.add(departures[n-1] == 21)

# Time-specific event constraints:
# Bucharest (city 1): meet friends between day 19 and day 21 → force arrival = 19.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Bucharest"],
             arrivals[i] == 19,
             True))
# Porto (city 3): wedding between day 5 and day 7 → force arrival = 5.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Porto"],
             arrivals[i] == 5,
             True))

# Connectivity constraints:
# Each consecutive pair of cities in the itinerary must be connected by a direct flight.
for i in range(n - 1):
    flight_options = []
    for pair in allowed_pairs:
        pair_list = list(pair)
        a, b = pair_list[0], pair_list[1]
        flight_options.append(And(order[i] == a, order[i+1] == b))
        flight_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(*flight_options))

# Solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:12s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")