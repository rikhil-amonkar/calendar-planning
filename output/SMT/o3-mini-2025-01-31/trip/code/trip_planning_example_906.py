from z3 import *

# City indices and durations:
# 0: Vilnius  (5 days)
# 1: Venice   (3 days)
# 2: Split    (5 days)
# 3: Riga     (2 days)
# 4: Paris    (5 days)
# 5: Geneva   (4 days)
# 6: Brussels (3 days)
cities = ["Vilnius", "Venice", "Split", "Riga", "Paris", "Geneva", "Brussels"]
durations = [5, 3, 5, 2, 5, 4, 3]

# Total raw days = 5+3+5+2+5+4+3 = 27.
# With 6 transitions (each sharing a flight day) the overall trip duration is 27 - 6 = 21 days.

# Allowed direct flights (bidirectional):
direct_flights = [
    ("Riga", "Paris"),
    ("Paris", "Venice"),
    ("Geneva", "Brussels"),
    ("Brussels", "Paris"),
    ("Vilnius", "Split"),
    ("Split", "Paris"),
    ("Geneva", "Paris"),
    ("Geneva", "Split"),
    ("Riga", "Vilnius"),  # given as "from Riga to Vilnius" but we assume bidirectional
    ("Brussels", "Riga"),
    ("Vilnius", "Paris"),
    ("Brussels", "Vilnius"),
    ("Brussels", "Venice")
]

# Create mapping from city name to index
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed unordered pairs (flights are bidirectional)
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

s = Solver()
n = len(cities)

# Define the order in which the cities are visited.
# order[i] is the index of the city visited at the i-th slot.
order = [Int("order_%i" % i) for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure days for each visit.
arrivals = [Int("arr_%i" % i) for i in range(n)]
departures = [Int("dep_%i" % i) for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# Connect each city's duration to its departure day.
# If a city with duration d is visited at position i, then: departure = arrival + d - 1.
for i in range(n):
    conds = []
    for city in range(n):
        conds.append(If(order[i] == city, departures[i] == arrivals[i] + durations[city] - 1, True))
    s.add(And(conds))

# Consecutive visits share the transit day:
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip ends on day 21.
s.add(departures[n-1] == 21)

# Extra time-specific constraints:

# 1. For Split (index 2): Wedding between day 11 and day 15.
#    Split's 5-day block is [arrival, arrival+4]; we require arrival <= 15 and arrival+4 >= 11.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Split"],
             And(arrivals[i] <= 15, arrivals[i] + 4 >= 11),
             True))

# 2. For Riga (index 3): Conference during day 6 and day 7.
#    Riga's block is 2 days, [arrival, arrival+1]. To cover day 6 and day 7, the only possibility is arrival == 6.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Riga"],
             arrivals[i] == 6,
             True))

# 3. For Geneva (index 5): Meet a friend between day 1 and day 4.
#    Geneva's 4-day block [arrival, arrival+3] must overlap [1,4]. It is sufficient to impose arrivals <= 4.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Geneva"],
             arrivals[i] <= 4,
             True))

# Connectivity constraints: consecutive cities in the itinerary must be connected by a direct flight.
for i in range(n-1):
    transition_options = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        transition_options.append(And(order[i] == a, order[i+1] == b))
        transition_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(transition_options))

# Find and print a solution.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_idx = m[order[i]].as_long()
        arrival_day = m[arrivals[i]].as_long()
        departure_day = m[departures[i]].as_long()
        itinerary.append((cities[city_idx], arrival_day, departure_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:10s} [{a}, {d}]")
else:
    print("No solution found")