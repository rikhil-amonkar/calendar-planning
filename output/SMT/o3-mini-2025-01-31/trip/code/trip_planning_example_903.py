from z3 import *

# City indices and durations:
# 0: Dubrovnik (5 days)
# 1: Helsinki  (5 days)
# 2: Vienna    (4 days)
# 3: Venice    (3 days)
# 4: Edinburgh (2 days)
# 5: Athens    (4 days)
# 6: Porto     (3 days)
cities = ["Dubrovnik", "Helsinki", "Vienna", "Venice", "Edinburgh", "Athens", "Porto"]
durations = [5, 5, 4, 3, 2, 4, 3]

# Total raw days = 5+5+4+3+2+4+3 = 26.
# With 6 transitions (flights sharing a day), total trip length = 26 - 6 = 20 days.

# Allowed direct flights (bidirectional) as given:
direct_flights = [
    ("Dubrovnik", "Vienna"),
    ("Vienna", "Venice"),
    ("Edinburgh", "Porto"),
    ("Dubrovnik", "Athens"),
    ("Athens", "Venice"),
    ("Helsinki", "Edinburgh"),
    ("Venice", "Edinburgh"),
    ("Dubrovnik", "Helsinki"),
    ("Vienna", "Porto"),
    ("Vienna", "Athens"),
    ("Athens", "Edinburgh"),
    ("Vienna", "Helsinki"),
    ("Venice", "Helsinki")
]

# Create a map from city name to index
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed pairs as a set of frozensets (order doesn't matter)
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

s = Solver()
n = len(cities)

# Define the order in which cities are visited.
# order[i] is the city index (0..6) in the i-th position.
order = [Int("order_%i" % i) for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure days for each city visit.
arrivals = [Int("arr_%i" % i) for i in range(n)]
departures = [Int("dep_%i" % i) for i in range(n)]

# The trip starts at day 1.
s.add(arrivals[0] == 1)

# Link the stay duration with departure day.
# For city j with duration d, if it is visited at position i then:
#   departures[i] = arrivals[i] + d - 1.
for i in range(n):
    case_constraints = []
    for city in range(n):
        case_constraints.append(If(order[i] == city, departures[i] == arrivals[i] + durations[city] - 1, True))
    s.add(And(case_constraints))

# Consecutive visits share the same flight day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The trip ends on day 20.
s.add(departures[n-1] == 20)

# Extra time constraints:

# 1. In Dubrovnik (index 0) you want to meet your friends between day 1 and day 5.
# Dubrovnik's block covers days [arrival, arrival+4].
# It must overlap with [1,5]: -> arrival <= 5 and (arrival+4) >= 1.
# (The second condition is always true given arrival>=1, but we include it for clarity.)
for i in range(n):
    s.add(If(order[i] == city_to_idx["Dubrovnik"],
             And(arrivals[i] <= 5, arrivals[i] + 4 >= 1),
             True))

# 2. In Athens (index 5) you are attending a wedding between day 8 and day 11.
# Athens' block covers days [arrival, arrival+3] and must overlap with [8,11]:
# That is: arrival <= 11 and (arrival+3) >= 8.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Athens"],
             And(arrivals[i] <= 11, arrivals[i] + 3 >= 8),
             True))

# Connectivity constraints: consecutive cities in the itinerary must be connected by a direct flight.
for i in range(n-1):
    allowed_transition = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        allowed_transition.append(And(order[i] == a, order[i+1] == b))
        allowed_transition.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(allowed_transition))

# Check for a solution and print the itinerary.
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
        print(f"  {city:12s} [{a}, {d}]")
else:
    print("No solution found")