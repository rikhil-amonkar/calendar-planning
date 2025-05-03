from z3 import *

# City indices and durations:
# 0: Riga     (5 days)  -- wedding between day 1 and day 5.
# 1: Geneva   (4 days)
# 2: Valencia (3 days)
# 3: Munich   (5 days)  -- annual show constraint is not given for Munich.
# 4: Venice   (4 days)
# 5: Athens   (3 days)  -- conference between day 16 and day 18.
# 6: Vilnius  (5 days)
cities = ["Riga", "Geneva", "Valencia", "Munich", "Venice", "Athens", "Vilnius"]
durations = [5, 4, 3, 5, 4, 3, 5]

# Total raw days = 5+4+3+5+4+3+5 = 29.
# With 6 transitions (each sharing one flight day), overall trip length = 29 - 6 = 23 days.

# Allowed direct flights (bidirectional):
# "from Vilnius to Munich, Geneva and Valencia"
# "from Riga to Munich, Venice and Athens"
# "Munich and Valencia"
# "Athens and Geneva"
# "Vilnius and Athens"
# "Munich and Geneva"
# "from Athens to Riga"
# "from Riga to Vilnius"
# "from Valencia to Athens"
# "Munich and Athens"
# "Munich and Venice"
direct_flights = [
    ("Vilnius", "Munich"),
    ("Vilnius", "Geneva"),
    ("Vilnius", "Valencia"),
    ("Riga", "Munich"),
    ("Riga", "Venice"),
    ("Riga", "Athens"),
    ("Munich", "Valencia"),
    ("Athens", "Geneva"),
    ("Vilnius", "Athens"),
    ("Munich", "Geneva"),
    ("Athens", "Riga"),
    ("Riga", "Vilnius"),
    ("Valencia", "Athens"),
    ("Munich", "Athens"),
    ("Munich", "Venice")
]

# Map city names to indices
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed pairs as unordered sets (flights are bidirectional)
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Create the Z3 solver.
s = Solver()
n = len(cities)

# Define the order in which the cities are visited.
# order[i] is the index of the city visited in position i.
order = [Int("order_%i" % i) for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure days for each city's visit.
arrivals = [Int("arr_%i" % i) for i in range(n)]
departures = [Int("dep_%i" % i) for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# Link each city’s duration to its departure day:
# For a city with duration d, when visited at position i, departure = arrival + d - 1.
for i in range(n):
    cons = []
    for c in range(n):
        cons.append(If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, True))
    s.add(And(cons))

# Consecutive visits share the same transit (flight) day.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must end on day 23.
s.add(departures[n-1] == 23)

# Extra time-specific constraints:

# 1. Wedding in Riga (city index 0) between day 1 and day 5.
# Riga's 5-day block is [arr, arr+4]. To have the wedding in that period, require:
#   arrival of Riga <= 5.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Riga"],
             arrivals[i] <= 5,
             True))

# 2. Conference in Athens (city index 5) between day 16 and day 18.
# Athens' 3-day block is [arr, arr+2]. To attend the conference, require:
#   arrival of Athens <= 18 and arrival+2 >= 16.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Athens"],
             And(arrivals[i] <= 18, arrivals[i] + 2 >= 16),
             True))

# Connectivity constraints:
# Each consecutive pair of cities in the itinerary must be connected by a direct flight.
for i in range(n-1):
    trans_options = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        trans_options.append(And(order[i] == a, order[i+1] == b))
        trans_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(trans_options))

# Find and print a solution if one exists.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_index = m[order[i]].as_long()
        a_day = m[arrivals[i]].as_long()
        d_day = m[departures[i]].as_long()
        itinerary.append((cities[city_index], a_day, d_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:10s} [{a}, {d}]")
else:
    print("No solution found")