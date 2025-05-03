from z3 import *

# City indices and durations:
# 0: Prague      (5 days) – Conference on day 8 and day 12 -> forces the 5‐day block to cover these days.
# 1: Berlin      (5 days) – Friends meet between day 1 and day 5.
# 2: London      (4 days)
# 3: Riga        (3 days) – Workshop between day 14 and day 16 -> forces the block to cover these days.
# 4: Vienna      (2 days)
# 5: Lyon        (2 days)
# 6: Manchester  (5 days)
cities = ["Prague", "Berlin", "London", "Riga", "Vienna", "Lyon", "Manchester"]
durations = [5, 5, 4, 3, 2, 2, 5]

# Total raw days = 5+5+4+3+2+2+5 = 26.
# There are 6 transitions (shared flight days), so overall trip length is 26 - 6 = 20 days.

# Allowed direct flights (bidirectional):
# • Prague and Riga             => (0,3)
# • London and Vienna           => (2,4)
# • London and Lyon             => (2,5)
# • Berlin and Manchester       => (1,6)
# • Berlin and Riga             => (1,3)
# • Vienna and Riga             => (4,3)
# • Prague and Manchester       => (0,6)
# • Prague and Lyon             => (0,5)
# • Berlin and Vienna           => (1,4)
# • Prague and Vienna           => (0,4)
# • Riga and Manchester         => (3,6)
# • Berlin and London           => (1,2)
# • London and Prague           => (2,0)
# • Lyon and Vienna             => (5,4)
# • Vienna and Manchester       => (4,6)
# • London and Manchester       => (2,6)
direct_flights = [
    ("Prague", "Riga"),
    ("London", "Vienna"),
    ("London", "Lyon"),
    ("Berlin", "Manchester"),
    ("Berlin", "Riga"),
    ("Vienna", "Riga"),
    ("Prague", "Manchester"),
    ("Prague", "Lyon"),
    ("Berlin", "Vienna"),
    ("Prague", "Vienna"),
    ("Riga", "Manchester"),
    ("Berlin", "London"),
    ("London", "Prague"),
    ("Lyon", "Vienna"),
    ("Vienna", "Manchester"),
    ("London", "Manchester")
]

# Map city names to indices.
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed unordered pairs (flights are bidirectional).
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Create Z3 solver instance.
s = Solver()
n = len(cities)

# Define the order in which the cities are visited (a permutation of 0..6).
order = [Int("order_%i" % i) for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure days for each visit.
arrivals = [Int("arr_%i" % i) for i in range(n)]
departures = [Int("dep_%i" % i) for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For a city with duration d, visited at slot i, enforce: departure = arrival + d - 1.
for i in range(n):
    conds = []
    for city in range(n):
        conds.append(If(order[i] == city, departures[i] == arrivals[i] + durations[city] - 1, True))
    s.add(And(conds))

# Each subsequent city starts on the same day the previous visit ends (flight day shared).
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 20.
s.add(departures[n-1] == 20)

# Extra time-specific constraints:

# 1. Prague (index 0): Must cover conference on day 8 and day 12.
#    Prague's 5-day block is [a, a+4]. For it to cover both day8 and day12 we require:
#         a <= 8    and    a+4 >= 12   which forces a == 8.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Prague"],
             arrivals[i] == 8,
             True))

# 2. Berlin (index 1): Friends meet between day 1 and day 5.
#    Berlin's block [a, a+4] must include some time in [1,5]. We require:
#         a <= 5.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Berlin"],
             arrivals[i] <= 5,
             True))

# 3. Riga (index 3): Workshop between day 14 and day 16.
#    Riga's 3-day block [a, a+2] must cover day14 and day16. This forces:
#         a <= 14   and   a+2 >= 16  => a == 14.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Riga"],
             arrivals[i] == 14,
             True))

# Connectivity: Consecutive cities in the itinerary must be connected by a direct flight.
for i in range(n-1):
    conn_options = []
    for pair in allowed_pairs:
        a, b = list(pair)
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(conn_options))

# Solve and print a solution if one exists.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_ind = m[order[i]].as_long()
        arr_day = m[arrivals[i]].as_long()
        dep_day = m[departures[i]].as_long()
        itinerary.append((cities[city_ind], arr_day, dep_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, start, end in itinerary:
        print(f"  {city:12s} [{start}, {end}]")
else:
    print("No solution found")