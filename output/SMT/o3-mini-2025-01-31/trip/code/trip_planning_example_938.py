from z3 import *

# We have 7 cities with the following durations and event constraints:
# 0: Krakow    (5 days) – Conference in Krakow between day 5 and day 9 forces arrival = 5 so that [5,9] is covered.
# 1: Florence  (4 days) – Visit relatives in Florence between day 14 and day 17 forces arrival = 14 so that [14,17] is covered.
# 2: Istanbul  (2 days)
# 3: Barcelona (2 days) – Meet a friend in Barcelona between day 1 and day 2 forces arrival = 1.
# 4: London    (3 days)
# 5: Dubrovnik (3 days)
# 6: Valencia  (4 days)
cities = ["Krakow", "Florence", "Istanbul", "Barcelona", "London", "Dubrovnik", "Valencia"]
durations = [5, 4, 2, 2, 3, 3, 4]

# Total raw days = 5+4+2+2+3+3+4 = 23.
# With 6 transitions (shared days between consecutive visits), the overall trip duration = 23 - 6 = 17 days.

# Allowed direct flights (bidirectional):
# - Barcelona and Krakow           -> (Barcelona, Krakow)         -> (3,0)
# - Barcelona and London            -> (Barcelona, London)          -> (3,4)
# - London and Florence             -> (London, Florence)           -> (4,1)
# - Barcelona and Dubrovnik         -> (Barcelona, Dubrovnik)       -> (3,5)
# - Istanbul and Krakow             -> (Istanbul, Krakow)           -> (2,0)
# - Barcelona and Istanbul          -> (Barcelona, Istanbul)        -> (3,2)
# - Barcelona and Florence          -> (Barcelona, Florence)        -> (3,1)
# - Barcelona and Valencia          -> (Barcelona, Valencia)        -> (3,6)
# - Valencia and London             -> (Valencia, London)           -> (6,4)
# - Istanbul and London             -> (Istanbul, London)           -> (2,4)
# - Krakow and London               -> (Krakow, London)             -> (0,4)
# - from Dubrovnik to Istanbul      -> (Dubrovnik, Istanbul)        -> (5,2)
# - Krakow and Valencia             -> (Krakow, Valencia)           -> (0,6)
# - Istanbul and Valencia           -> (Istanbul, Valencia)         -> (2,6)
direct_flights = [
    ("Barcelona", "Krakow"),
    ("Barcelona", "London"),
    ("London", "Florence"),
    ("Barcelona", "Dubrovnik"),
    ("Istanbul", "Krakow"),
    ("Barcelona", "Istanbul"),
    ("Barcelona", "Florence"),
    ("Barcelona", "Valencia"),
    ("Valencia", "London"),
    ("Istanbul", "London"),
    ("Krakow", "London"),
    ("Dubrovnik", "Istanbul"),
    ("Krakow", "Valencia"),
    ("Istanbul", "Valencia")
]

# Map city names to indices.
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Build allowed unordered flight pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Set up the Z3 solver.
s = Solver()
n = len(cities)

# Define the visitation order as a permutation of city indices.
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
#   departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day: arrival of visit i+1 equals departure of visit i.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 17.
s.add(departures[n-1] == 17)

# Time-specific event constraints:
# Krakow (city 0): Conference between day 5 and day 9 ⇒ force arrival = 5.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Krakow"],
             arrivals[i] == 5,
             True))

# Florence (city 1): Visit relatives between day 14 and day 17 ⇒ force arrival = 14.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Florence"],
             arrivals[i] == 14,
             True))

# Barcelona (city 3): Meet a friend between day 1 and day 2 ⇒ force arrival = 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Barcelona"],
             arrivals[i] == 1,
             True))

# Connectivity constraints:
# Each consecutive pair in the itinerary must be connected by a direct flight.
for i in range(n - 1):
    flight_options = []
    for pair in allowed_pairs:
        # Unpack the unordered pair.
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