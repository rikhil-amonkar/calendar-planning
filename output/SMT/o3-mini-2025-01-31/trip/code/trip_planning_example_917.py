from z3 import *

# City indices and durations:
# 0: Mykonos   (3 days) – Conference in Mykonos during day 21 and day 23; thus, Mykonos must be [21,23].
# 1: Dubrovnik (4 days)
# 2: Barcelona (5 days)
# 3: London    (5 days)
# 4: Milan     (3 days) – Annual show in Milan from day 9 to day 11; thus, Milan must be [9,11].
# 5: Rome      (4 days)
# 6: Hamburg   (5 days) – Workshop in Hamburg between day 1 and day 5; hence, Hamburg must be [1,5].
cities = ["Mykonos", "Dubrovnik", "Barcelona", "London", "Milan", "Rome", "Hamburg"]
durations = [3, 4, 5, 5, 3, 4, 5]

# Total raw days = 3+4+5+5+3+4+5 = 29.
# There are 6 transitions (shared flight days), so overall trip length = 29 - 6 = 23 days.

# Allowed direct flights (bidirectional):
# Hamburg and Milan       -> (Hamburg, Milan)       -> (6, 4)
# Barcelona and Rome      -> (Barcelona, Rome)      -> (2, 5)
# Barcelona and Dubrovnik -> (Barcelona, Dubrovnik) -> (2, 1)
# London and Mykonos      -> (London, Mykonos)      -> (3, 0)
# Milan and Barcelona     -> (Milan, Barcelona)     -> (4, 2)
# London and Barcelona    -> (London, Barcelona)    -> (3, 2)
# Hamburg and Barcelona   -> (Hamburg, Barcelona)   -> (6, 2)
# London and Milan        -> (London, Milan)        -> (3, 4)
# Hamburg and Rome        -> (Hamburg, Rome)        -> (6, 5)
# Dubrovnik and Rome      -> (Dubrovnik, Rome)      -> (1, 5)
# Hamburg and London      -> (Hamburg, London)      -> (6, 3)
# Milan and Mykonos       -> (Milan, Mykonos)       -> (4, 0)
# London and Rome         -> (London, Rome)         -> (3, 5)
# Rome and Mykonos        -> (Rome, Mykonos)        -> (5, 0)
direct_flights = [
    ("Hamburg", "Milan"),
    ("Barcelona", "Rome"),
    ("Barcelona", "Dubrovnik"),
    ("London", "Mykonos"),
    ("Milan", "Barcelona"),
    ("London", "Barcelona"),
    ("Hamburg", "Barcelona"),
    ("London", "Milan"),
    ("Hamburg", "Rome"),
    ("Dubrovnik", "Rome"),
    ("Hamburg", "London"),
    ("Milan", "Mykonos"),
    ("London", "Rome"),
    ("Rome", "Mykonos")
]

# Map city names to indices.
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed unordered pairs for connectivity.
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({ city_to_idx[a], city_to_idx[b] }))

s = Solver()
n = len(cities)

# Define order in which cities are visited: a permutation of [0,1,...,6].
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit slot.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the city is c then departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the flight (transit) day:
# The next city's arrival equals the previous visit's departure.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 23.
s.add(departures[n-1] == 23)

# Time-specific constraints:
# 1. Mykonos (index 0): Conference during day 21 and day 23 requires Mykonos's block [a, a+2] to include day 21 and day 23.
#    The only possibility is a == 21.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Mykonos"],
             arrivals[i] == 21,
             True))

# 2. Milan (index 4): Annual show in Milan from day 9 to day 11 requires Milan's block [a, a+2] to be exactly [9,11].
for i in range(n):
    s.add(If(order[i] == city_to_idx["Milan"],
             arrivals[i] == 9,
             True))

# 3. Hamburg (index 6): Workshop in Hamburg between day 1 and day 5; with a 5-day block, it must cover days1-5,
#    so we force Hamburg's arrival to be 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Hamburg"],
             arrivals[i] == 1,
             True))

# Connectivity constraints:
# Each consecutive pair of cities in the itinerary must have a direct flight between them.
for i in range(n - 1):
    conn_options = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(conn_options))

# Solve and print the itinerary if a solution is found.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_idx = m.eval(order[i]).as_long()
        start_day = m.eval(arrivals[i]).as_long()
        end_day = m.eval(departures[i]).as_long()
        itinerary.append((cities[city_idx], start_day, end_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:10s} [{a}, {d}]")
else:
    print("No solution found")