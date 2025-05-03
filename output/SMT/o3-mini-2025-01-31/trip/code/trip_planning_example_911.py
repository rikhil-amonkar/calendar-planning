from z3 import *

# City indices and durations:
# 0: Dubrovnik (5 days) – Annual show: must be in Dubrovnik from day 13 to day 17.
# 1: Krakow    (3 days)
# 2: Stuttgart (5 days)
# 3: Oslo      (3 days) – Workshop: attend between day 11 and day 13.
# 4: Copenhagen(2 days)
# 5: Istanbul  (5 days) – Meet friends between day 5 and day 9.
# 6: Split     (5 days)
cities = ["Dubrovnik", "Krakow", "Stuttgart", "Oslo", "Copenhagen", "Istanbul", "Split"]
durations = [5, 3, 5, 3, 2, 5, 5]

# Total raw days = 5 + 3 + 5 + 3 + 2 + 5 + 5 = 28.
# There will be 6 transit days (one per flight between successive cities),
# so the overall trip length is 28 - 6 = 22 days.

# Allowed direct flights (bidirectional):
# • Oslo and Split
# • Stuttgart and Krakow
# • Oslo and Dubrovnik
# • Stuttgart and Copenhagen
# • Istanbul and Copenhagen
# • Krakow and Copenhagen
# • Copenhagen and Split
# • Krakow and Oslo
# • Stuttgart and Istanbul
# • from Dubrovnik to Istanbul
# • Dubrovnik and Copenhagen
# • Oslo and Copenhagen
# • Krakow and Split
# • Istanbul and Krakow
# • Istanbul and Oslo
# • Stuttgart and Split
direct_flights = [
    ("Oslo", "Split"),
    ("Stuttgart", "Krakow"),
    ("Oslo", "Dubrovnik"),
    ("Stuttgart", "Copenhagen"),
    ("Istanbul", "Copenhagen"),
    ("Krakow", "Copenhagen"),
    ("Copenhagen", "Split"),
    ("Krakow", "Oslo"),
    ("Stuttgart", "Istanbul"),
    ("Dubrovnik", "Istanbul"),
    ("Dubrovnik", "Copenhagen"),
    ("Oslo", "Copenhagen"),
    ("Krakow", "Split"),
    ("Istanbul", "Krakow"),
    ("Istanbul", "Oslo"),
    ("Stuttgart", "Split")
]

# Map city names to indices.
city_to_idx = {name: idx for idx, name in enumerate(cities)}

# Build allowed unordered pairs (since flights are bidirectional).
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

s = Solver()
n = len(cities)

# Define visit order (a permutation of {0,...,6}).
order = [Int("order_%i" % i) for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure days for each city visit.
arrivals = [Int("arr_%i" % i) for i in range(n)]
departures = [Int("dep_%i" % i) for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For a visit at slot i, if the city has duration d then departure = arrival + d - 1.
for i in range(n):
    cs = []
    for city in range(n):
        cs.append(If(order[i] == city, departures[i] == arrivals[i] + durations[city] - 1, True))
    s.add(And(cs))

# Consecutive visits share a transit (flight) day:
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must end on day 22.
s.add(departures[n-1] == 22)

# Extra time-specific constraints:

# 1. In Dubrovnik (index 0): Annual show from day 13 to day 17.
#    Dubrovnik's 5-day block [a, a+4] must fully cover days 13 to 17.
#    This forces the block to be exactly days 13 to 17, i.e. arrival == 13.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Dubrovnik"],
             arrivals[i] == 13,
             True))

# 2. In Oslo (index 3): Workshop between day 11 and day 13.
#    Oslo's 3-day block [a, a+2] must include days 11 to 13, which forces arrival == 11.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Oslo"],
             arrivals[i] == 11,
             True))

# 3. In Istanbul (index 5): Meet friends between day 5 and day 9.
#    Istanbul's 5-day block [a, a+4] must overlap with [5, 9]. We require:
#      a <= 9   and   a + 4 >= 5.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Istanbul"],
             And(arrivals[i] <= 9, arrivals[i] + 4 >= 5),
             True))

# Connectivity: consecutive cities must be connected by a direct flight.
for i in range(n-1):
    trans_opts = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        trans_opts.append(And(order[i] == a, order[i+1] == b))
        trans_opts.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(trans_opts))

# Solve the constraints and print the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_idx = m.eval(order[i]).as_long()
        a_day = m.eval(arrivals[i]).as_long()
        d_day = m.eval(departures[i]).as_long()
        itinerary.append((cities[city_idx], a_day, d_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:12s} [{a}, {d}]")
else:
    print("No solution found")