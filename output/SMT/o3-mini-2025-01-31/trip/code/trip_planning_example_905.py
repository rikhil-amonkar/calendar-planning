from z3 import *

# City indices and durations:
# 0: Dubrovnik (2 days)
# 1: Riga       (4 days) -- workshop in Riga between day 1 and day 4 (i.e. Riga's 4‐day block must intersect [1,4])
# 2: Reykjavik  (4 days)
# 3: Geneva     (5 days) -- visit relatives in Geneva between day 6 and day 10 (i.e. Geneva's block must intersect [6,10])
# 4: Zurich     (2 days)
# 5: Brussels   (2 days)
# 6: Helsinki   (2 days) -- meet a friend in Helsinki between day 14 and day 15 (i.e. Helsinki's block must intersect [14,15])
cities = ["Dubrovnik", "Riga", "Reykjavik", "Geneva", "Zurich", "Brussels", "Helsinki"]
durations = [2, 4, 4, 5, 2, 2, 2]

# Sum of durations = 2+4+4+5+2+2+2 = 21.
# Considering that each transition shares one day (6 transitions), the trip length is 21 - 6 = 15 days.

# Allowed direct flights (bidirectional) provided:
direct_flights = [
    ("Zurich", "Helsinki"),
    ("Reykjavik", "Helsinki"),
    ("Brussels", "Helsinki"),
    ("Riga", "Helsinki"),
    ("Riga", "Brussels"),
    ("Brussels", "Reykjavik"),
    ("Geneva", "Helsinki"),
    ("Dubrovnik", "Helsinki"),
    ("Zurich", "Brussels"),
    ("Riga", "Zurich"),
    ("Geneva", "Brussels"),
    ("Zurich", "Geneva"),
    ("Zurich", "Reykjavik"),
    ("Zurich", "Dubrovnik"),
    ("Dubrovnik", "Geneva")
]

# Create mapping from city name to index
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed unordered pairs as frozensets
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

s = Solver()
n = len(cities)

# Define the order in which the cities are visited 
order = [Int("order_%i" % i) for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure days for each visit.
arrivals = [Int("arr_%i" % i) for i in range(n)]
departures = [Int("dep_%i" % i) for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# Link each city’s duration with its departure:
# If city `c` at position i is visited and its duration is d, then departures[i] = arrivals[i] + d - 1.
for i in range(n):
    city_duration_cases = []
    for city in range(n):
        city_duration_cases.append(If(order[i] == city, departures[i] == arrivals[i] + durations[city] - 1, True))
    s.add(And(city_duration_cases))

# Consecutive visits share the flight day: the arrival of the next city equals the departure day of the current city.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip ends on day 15.
s.add(departures[n-1] == 15)

# Extra time-specific constraints:

# 1. Riga: 4-day block [arr, arr+3] should include the workshop between day 1 and day 4.
#    This is enforced by ensuring the block intersects [1,4]. Since arrivals are >= 1,
#    a sufficient constraint is: arrival_Riga <= 4.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Riga"],
             arrivals[i] <= 4,  # ensures that the 4-day block [arr, arr+3] touches [1,4]
             True))

# 2. Geneva: 5-day block [arr, arr+4] must overlap [6,10], i.e. arrival <= 10 and arrival+4 >= 6.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Geneva"],
             And(arrivals[i] <= 10, arrivals[i] + 4 >= 6),
             True))

# 3. Helsinki: 2-day block [arr, arr+1] must overlap [14,15], i.e. arrival <= 15 and arrival+1 >= 14.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Helsinki"],
             And(arrivals[i] <= 15, arrivals[i] + 1 >= 14),
             True))

# Connectivity constraints: consecutive cities must have a direct flight connection.
for i in range(n-1):
    connection_options = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        connection_options.append(And(order[i] == a, order[i+1] == b))
        connection_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(connection_options))

# Try to find a solution.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_index = m[order[i]].as_long()
        a_day = m[arrivals[i]].as_long()
        d_day = m[departures[i]].as_long()
        itinerary.append((cities[city_index], a_day, d_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, start, end in itinerary:
        print(f"  {city:12s} [{start}, {end}]")
else:
    print("No solution found")