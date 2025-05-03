from z3 import *

# City indices and durations:
# 0: Oslo      (5 days) – Workshop in Oslo between day 1 and day 5.
# 1: Copenhagen(4 days)
# 2: Vilnius   (5 days) – Visit relatives in Vilnius between day 13 and day 17.
# 3: Salzburg  (5 days)
# 4: Tallinn   (2 days)
# 5: Geneva    (5 days)
# 6: Frankfurt (5 days)
cities = ["Oslo", "Copenhagen", "Vilnius", "Salzburg", "Tallinn", "Geneva", "Frankfurt"]
durations = [5, 4, 5, 5, 2, 5, 5]

# Total raw days: 5+4+5+5+2+5+5 = 31.
# There are 6 transitions (shared flight days), so overall trip length = 31 - 6 = 25 days.

# Allowed direct flights (assumed bidirectional):
direct_flights = [
    ("Copenhagen", "Frankfurt"),
    ("Oslo", "Vilnius"),
    ("Tallinn", "Frankfurt"),
    ("Vilnius", "Frankfurt"),
    ("Oslo", "Geneva"),
    ("Tallinn", "Vilnius"),   # given as "from Tallinn to Vilnius", assumed bidirectional.
    ("Copenhagen", "Vilnius"),
    ("Oslo", "Tallinn"),
    ("Oslo", "Frankfurt"),
    ("Geneva", "Frankfurt"),
    ("Geneva", "Copenhagen"),
    ("Frankfurt", "Salzburg"),
    ("Copenhagen", "Tallinn"),
    ("Oslo", "Copenhagen")
]

# Map city names to indices.
city_to_idx = { name: idx for idx, name in enumerate(cities) }

# Build allowed unordered pairs for connectivity.
allowed_pairs = set()
for (a, b) in direct_flights:
    allowed_pairs.add(frozenset({ city_to_idx[a], city_to_idx[b] }))

# Create Z3 solver instance.
s = Solver()
n = len(cities)

# Define order in which cities are visited: a permutation of {0,1,...,6}.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit slot.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit in slot i, if the city has duration d then:
# departure = arrival + d - 1.
for i in range(n):
    conds = []
    for city in range(n):
        conds.append(If(order[i] == city, departures[i] == arrivals[i] + durations[city] - 1, True))
    s.add(And(conds))

# Consecutive visits share the transit (flight) day; 
# that is, the next city's arrival day equals the previous departure day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 25.
s.add(departures[n-1] == 25)

# Extra time-specific constraints:

# 1. Oslo (index 0): Workshop must be attended between day 1 and day 5.
#    Oslo's 5-day block is [a, a+4]. To ensure the workshop takes place in that block
#    and given our trip starts at day 1, we force Oslo's visit to be exactly days 1-5.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Oslo"],
             arrivals[i] == 1,
             True))

# 2. Vilnius (index 2): Visit relatives between day 13 and day 17.
#    Vilnius's 5-day block is [a, a+4]. To have the block overlap the interval [13,17],
#    we need: a <= 17 and a+4 >= 13.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Vilnius"],
             And(arrivals[i] <= 17, arrivals[i] + 4 >= 13),
             True))

# Connectivity constraints:
# Each consecutive pair of cities in the itinerary must have a direct flight according to allowed_pairs.
for i in range(n - 1):
    conn_options = []
    for pair in allowed_pairs:
        lst = list(pair)
        a, b = lst[0], lst[1]
        conn_options.append(And(order[i] == a, order[i+1] == b))
        conn_options.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(conn_options))

# Solve the constraints and output the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_index = m.eval(order[i]).as_long()
        start_day = m.eval(arrivals[i]).as_long()
        end_day = m.eval(departures[i]).as_long()
        itinerary.append((cities[city_index], start_day, end_day))
    print("Itinerary (City, arrival day, departure day):")
    for city, a, d in itinerary:
        print(f"  {city:10s} [{a}, {d}]")
else:
    print("No solution found")