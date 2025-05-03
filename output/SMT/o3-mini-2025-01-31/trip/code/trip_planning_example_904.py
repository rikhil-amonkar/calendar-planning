from z3 import *

# City indices and durations:
# 0: Bucharest (5 days)
# 1: Istanbul (2 days)
# 2: Seville   (4 days)
# 3: Brussels  (3 days)
# 4: Split     (3 days)
# 5: Geneva    (4 days)
# 6: Budapest  (5 days)
cities = ["Bucharest", "Istanbul", "Seville", "Brussels", "Split", "Geneva", "Budapest"]
durations = [5, 2, 4, 3, 3, 4, 5]

# Total raw days = 5+2+4+3+3+4+5 = 26.
# With 6 overnight flights (sharing one day each), overall trip length = 26 - 6 = 20 days.

# Allowed direct flights (bidirectional) as given:
direct_flights = [
    ("Budapest", "Brussels"),
    ("Geneva", "Brussels"),
    ("Istanbul", "Brussels"),
    ("Split", "Geneva"),
    ("Geneva", "Budapest"),
    ("Budapest", "Bucharest"),
    ("Budapest", "Istanbul"),
    ("Bucharest", "Brussels"),
    ("Brussels", "Seville"),
    ("Istanbul", "Bucharest"),
    ("Geneva", "Istanbul")
]

# Map city names to indices for easier handling
city_to_idx = {name: idx for idx, name in enumerate(cities)}

# Build allowed pairs as a set of frozensets (since flights are bidirectional)
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

s = Solver()
n = len(cities)

# Define the order in which the cities are visited.
order = [Int("order_%i" % i) for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day for each visit.
arrivals = [Int("arr_%i" % i) for i in range(n)]
departures = [Int("dep_%i" % i) for i in range(n)]

# The trip begins at day 1.
s.add(arrivals[0] == 1)

# Link each city's duration with its departure day.
# If a city with duration d is visited at time i, then: departure = arrival + d - 1.
for i in range(n):
    city_duration_cases = []
    for city in range(n):
        city_duration_cases.append(
            If(order[i] == city, departures[i] == arrivals[i] + durations[city] - 1, True)
        )
    s.add(And(city_duration_cases))

# Consecutive visits share the same flight day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The trip must finish at day 20.
s.add(departures[n-1] == 20)

# Extra time-specific constraints:

# 1. In Istanbul (city index 1) you plan to visit relatives between day 10 and 11.
# Istanbul has a 2-day block: [arrival, arrival+1]. It must overlap [10,11]:
# i.e., arrival <= 11 and arrival+1 >= 10.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Istanbul"],
             And(arrivals[i] <= 11, arrivals[i] + 1 >= 10),
             True))

# 2. In Brussels (city index 3) there is an annual show from day 15 to day 17.
# Brussels has a 3-day block: [arrival, arrival+2]. It must overlap [15,17]:
# i.e., arrival <= 17 and arrival+2 >= 15.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Brussels"],
             And(arrivals[i] <= 17, arrivals[i] + 2 >= 15),
             True))

# Connectivity constraints: each pair of consecutive cities in the itinerary must be connected by a direct flight.
for i in range(n - 1):
    possible_connections = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        possible_connections.append(And(order[i] == a, order[i+1] == b))
        possible_connections.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(possible_connections))

# Try to find a solution
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