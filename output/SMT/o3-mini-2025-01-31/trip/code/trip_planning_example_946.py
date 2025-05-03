from z3 import *

# Cities and durations:
# 0: Vilnius   (4 days)
# 1: Zurich    (5 days)
# 2: Stuttgart (4 days) – Visit relatives between day 1 and 4, so force arrival = 1.
# 3: Lyon      (2 days) – Annual show from day 19 to 20, so force arrival = 19.
# 4: Athens    (5 days)
# 5: Madrid    (2 days)
# 6: Helsinki  (4 days) – Meet friend between day 11 and 14, so force arrival = 11.
#
# Total raw days = 4+5+4+2+5+2+4 = 26.
# There are 6 transitions (each shared day), so overall trip length = 26 - 6 = 20 days.
cities = ["Vilnius", "Zurich", "Stuttgart", "Lyon", "Athens", "Madrid", "Helsinki"]
durations = [4, 5, 4, 2, 5, 2, 4]

# Allowed direct flights (bidirectional):
# 1. Athens and Madrid      -> {Athens, Madrid}       -> {4,5}
# 2. Zurich and Madrid      -> {Zurich, Madrid}       -> {1,5}
# 3. Athens and Zurich      -> {Athens, Zurich}       -> {4,1}
# 4. Vilnius and Zurich     -> {Vilnius, Zurich}      -> {0,1}
# 5. Helsinki and Madrid    -> {Helsinki, Madrid}     -> {6,5}
# 6. Helsinki and Zurich    -> {Helsinki, Zurich}     -> {6,1}
# 7. Vilnius and Helsinki   -> {Vilnius, Helsinki}    -> {0,6}
# 8. Madrid and Lyon        -> {Madrid, Lyon}         -> {5,3}
# 9. Stuttgart and Athens   -> {Stuttgart, Athens}    -> {2,4}
# 10. Athens and Vilnius    -> {Athens, Vilnius}      -> {4,0}
direct_flights = [
    ("Athens", "Madrid"),
    ("Zurich", "Madrid"),
    ("Athens", "Zurich"),
    ("Vilnius", "Zurich"),
    ("Helsinki", "Madrid"),
    ("Helsinki", "Zurich"),
    ("Vilnius", "Helsinki"),
    ("Madrid", "Lyon"),
    ("Stuttgart", "Athens"),
    ("Athens", "Vilnius")
]

# Map city names to indices.
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Build allowed flight connections as unordered pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Z3 solver setup.
s = Solver()
n = len(cities)  # number of cities (7)

# Define visitation order as a permutation of the 7 cities.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit, departure = arrival + duration - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: arrival of next equals departure of previous.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 20.
s.add(departures[n-1] == 20)

# Time-specific event constraints:
# Stuttgart (index 2): relatives between day 1 and 4 -> force arrival = 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Stuttgart"], arrivals[i] == 1, True))
# Lyon (index 3): annual show from day 19 to 20 -> force arrival = 19.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Lyon"], arrivals[i] == 19, True))
# Helsinki (index 6): meet friend between day 11 and 14 -> force arrival = 11.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Helsinki"], arrivals[i] == 11, True))

# Connectivity constraints:
# Ensure each consecutive pair in the itinerary has a direct flight connection.
for i in range(n - 1):
    opts = []
    for pair in allowed_pairs:
        pl = list(pair)
        a, b = pl[0], pl[1]
        opts.append(And(order[i] == a, order[i+1] == b))
        opts.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(*opts))

# Solve and output solution.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:10s}: [{a_day}, {d_day}]")
else:
    print("No solution found")