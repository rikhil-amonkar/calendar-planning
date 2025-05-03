from z3 import *

# City indices and durations:
# 0: Helsinki (5 days)
# 1: Riga     (3 days)
# 2: Milan    (2 days)  -- with relatives visit between day 8 and day 9
# 3: Lyon     (2 days)
# 4: Tallinn  (2 days)
# 5: Geneva   (4 days)  -- conference during day 1 and day 4
# 6: Munich   (3 days)
cities = ["Helsinki", "Riga", "Milan", "Lyon", "Tallinn", "Geneva", "Munich"]
durations = [5, 3, 2, 2, 2, 4, 3]

# Total raw days = 5+3+2+2+2+4+3 = 21.
# With 6 transitions (shared flight days), effective trip length = 21 - 6 = 15 days.

# Allowed direct flights (bidirectional):
direct_flights = [
    ("Milan", "Riga"),
    ("Riga", "Munich"),      # provided as "from Riga to Munich"
    ("Riga", "Tallinn"),     # provided as "from Riga to Tallinn"
    ("Helsinki", "Milan"),
    ("Helsinki", "Riga"),
    ("Milan", "Munich"),
    ("Helsinki", "Tallinn"),
    ("Munich", "Lyon"),
    ("Helsinki", "Munich"),
    ("Tallinn", "Munich"),
    ("Geneva", "Munich"),
    ("Geneva", "Helsinki")
]

# Create mapping from city name to index:
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed pairs (as unordered frozensets, since flights are bidirectional)
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

s = Solver()
n = len(cities)

# Define the order in which cities are visited.
# order[i] is the index of the city visited in the i-th slot.
order = [Int("order_%i" % i) for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure days for each city visit.
arrivals = [Int("arr_%i" % i) for i in range(n)]
departures = [Int("dep_%i" % i) for i in range(n)]

# The trip starts at day 1.
s.add(arrivals[0] == 1)

# Link each city's duration with its departure day:
# If a city with duration d is visited at position i, then departure = arrival + d - 1.
for i in range(n):
    duration_constraints = []
    for city in range(n):
        duration_constraints.append(
            If(order[i] == city, departures[i] == arrivals[i] + durations[city] - 1, True)
        )
    s.add(And(duration_constraints))

# Consecutive visits share the transit day:
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip ends on day 15.
s.add(departures[n-1] == 15)

# Extra time-specific constraints:

# 1. Milan (city index 2): Visit relatives between day 8 and day 9.
# Milan's block is 2 days: [arrival, arrival+1]. It must overlap [8,9]:
#   arrival <= 9 and arrival+1 >= 8.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Milan"],
             And(arrivals[i] <= 9, arrivals[i] + 1 >= 8),
             True))

# 2. Geneva (city index 5): Conference between day 1 and day 4.
# Geneva's block is 4 days: [arrival, arrival+3]. It must intersect [1,4]:
#   arrival <= 4. (and implicitly arrival+3 >= 1 since arrivals>=1)
for i in range(n):
    s.add(If(order[i] == city_to_idx["Geneva"],
             arrivals[i] <= 4,
             True))

# Connectivity constraints: consecutive cities must have a direct flight connection.
for i in range(n-1):
    possible_transitions = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        possible_transitions.append(And(order[i] == a, order[i+1] == b))
        possible_transitions.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(possible_transitions))

# Solve and print the itinerary if found.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_idx = m[order[i]].as_long()
        a_day = m[arrivals[i]].as_long()
        d_day = m[departures[i]].as_long()
        itinerary.append((cities[city_idx], a_day, d_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:10s} [{a}, {d}]")
else:
    print("No solution found")