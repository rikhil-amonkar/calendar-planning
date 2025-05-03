from z3 import *

# City indices and durations:
# 0: Bucharest (3 days)
# 1: Venice    (5 days) – Wedding between day 22 and day 26.
# 2: Prague    (4 days)
# 3: Frankfurt (5 days) – Annual show between day 12 and day 16.
# 4: Zurich    (5 days)
# 5: Florence  (5 days)
# 6: Tallinn   (5 days) – Meet friends between day 8 and day 12.
cities = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]
durations = [3, 5, 4, 5, 5, 5, 5]

# Total raw days = 3+5+4+5+5+5+5 = 32.
# There are 6 transitions (each flight day is shared), so overall trip length = 32 - 6 = 26 days.

# Allowed direct flights (bidirectional):
# - Prague and Tallinn          => (Prague, Tallinn)        (2,6)
# - Prague and Zurich           => (Prague, Zurich)         (2,4)
# - Florence and Prague         => (Florence, Prague)       (5,2)
# - Frankfurt and Bucharest     => (Frankfurt, Bucharest)   (3,0)
# - Frankfurt and Venice        => (Frankfurt, Venice)      (3,1)
# - Prague and Bucharest        => (Prague, Bucharest)      (2,0)
# - Bucharest and Zurich        => (Bucharest, Zurich)      (0,4)
# - Tallinn and Frankfurt       => (Tallinn, Frankfurt)     (6,3)
# - from Zurich to Florence     => (Zurich, Florence)       (4,5)  [treated bidirectionally]
# - Frankfurt and Zurich        => (Frankfurt, Zurich)      (3,4)
# - Zurich and Venice           => (Zurich, Venice)         (4,1)
# - Florence and Frankfurt      => (Florence, Frankfurt)    (5,3)
# - Prague and Frankfurt        => (Prague, Frankfurt)      (2,3)
# - Tallinn and Zurich          => (Tallinn, Zurich)        (6,4)
direct_flights = [
    ("Prague", "Tallinn"),
    ("Prague", "Zurich"),
    ("Florence", "Prague"),
    ("Frankfurt", "Bucharest"),
    ("Frankfurt", "Venice"),
    ("Prague", "Bucharest"),
    ("Bucharest", "Zurich"),
    ("Tallinn", "Frankfurt"),
    ("Zurich", "Florence"),
    ("Frankfurt", "Zurich"),
    ("Zurich", "Venice"),
    ("Florence", "Frankfurt"),
    ("Prague", "Frankfurt"),
    ("Tallinn", "Zurich")
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

# Define a permutation 'order' representing the visitation order of the cities.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure days for each visit slot.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit in slot i, if the city visited is 'c' then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    constraints = []
    for c in range(n):
        constraints.append(If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, True))
    s.add(And(constraints))

# Consecutive visits share a flight day.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 26.
s.add(departures[n-1] == 26)

# Time-specific constraints:
# 1. Venice (index 1): Wedding between day 22 and day 26.
#    Venice's block is [a, a+4]. We need: a <= 26 and a+4 >= 22.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Venice"],
             And(arrivals[i] <= 26, arrivals[i] + 4 >= 22),
             True))

# 2. Frankfurt (index 3): Annual show between day 12 and day 16.
#    Frankfurt's block is [a, a+4]. Enforce: a <= 16 and a+4 >= 12.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Frankfurt"],
             And(arrivals[i] <= 16, arrivals[i] + 4 >= 12),
             True))

# 3. Tallinn (index 6): Meet friends between day 8 and day 12.
#    Tallinn's block is [a, a+4]. Enforce: a <= 12 and a+4 >= 8.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Tallinn"],
             And(arrivals[i] <= 12, arrivals[i] + 4 >= 8),
             True))

# Connectivity constraints:
# Each consecutive pair of cities must be connected by a direct flight.
for i in range(n-1):
    conn_options = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(conn_options))

# Solve and print the itinerary if one is found.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_index = m.eval(order[i]).as_long()
        arrival_day = m.eval(arrivals[i]).as_long()
        departure_day = m.eval(departures[i]).as_long()
        itinerary.append((cities[city_index], arrival_day, departure_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, start, end in itinerary:
        print(f"  {city:10s} [{start}, {end}]")
else:
    print("No solution found")