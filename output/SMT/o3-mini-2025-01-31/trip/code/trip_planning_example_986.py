from z3 import *

# City indices and durations:
# 0: Lisbon   (3 days)  – Wedding in Lisbon between day 1 and day 3 → force arrival = 1.
# 1: Hamburg  (5 days)  – Annual show in Hamburg from day 13 to day 17 → force arrival = 13.
# 2: Brussels (4 days)
# 3: Geneva   (4 days)
# 4: Santorini(2 days)
# 5: Helsinki (5 days)
# 6: Lyon     (4 days)
#
# Total raw days = 3 + 5 + 4 + 4 + 2 + 5 + 4 = 27.
# With 6 overlapping days when transferring between 7 cities, the overall trip is 27 - 6 = 21 days.

cities = ["Lisbon", "Hamburg", "Brussels", "Geneva", "Santorini", "Helsinki", "Lyon"]
durations = [3, 5, 4, 4, 2, 5, 4]

# Allowed direct flights:
# - Lisbon and Hamburg
# - Brussels and Geneva
# - Lisbon and Geneva
# - Helsinki and Geneva
# - Lisbon and Helsinki
# - Brussels and Helsinki
# - Lisbon and Lyon
# - Lyon and Brussels
# - Lisbon and Brussels
# - Geneva and Santorini
# - Helsinki and Hamburg
# - from Hamburg to Geneva (one-way)
# - Brussels and Hamburg

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# Lisbon <-> Hamburg
add_bidirectional(0, 1)
# Brussels <-> Geneva
add_bidirectional(2, 3)
# Lisbon <-> Geneva
add_bidirectional(0, 3)
# Helsinki <-> Geneva
add_bidirectional(5, 3)
# Lisbon <-> Helsinki
add_bidirectional(0, 5)
# Brussels <-> Helsinki
add_bidirectional(2, 5)
# Lisbon <-> Lyon
add_bidirectional(0, 6)
# Lyon <-> Brussels
add_bidirectional(6, 2)
# Lisbon <-> Brussels
add_bidirectional(0, 2)
# Geneva <-> Santorini
add_bidirectional(3, 4)
# Helsinki <-> Hamburg
add_bidirectional(5, 1)
# Add one-way flight from Hamburg to Geneva
allowed_flights.append((1, 3))
# Brussels <-> Hamburg
add_bidirectional(2, 1)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# The itinerary order is modeled as a permutation of city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit at position i, if city c is visited then its departure day is:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: the arrival day of the next city equals the departure day of the previous city.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 21.
s.add(departures[n-1] == 21)

# Event-specific constraints:
# Lisbon (index 0): Wedding between day 1 and day 3 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 1, True))
# Hamburg (index 1): Annual show from day 13 to day 17 → force arrival = 13.
for i in range(n):
    s.add(If(order[i] == 1, arrivals[i] == 13, True))

# Connectivity constraints:
# Each consecutive pair of visited cities must be linked by an allowed direct flight.
for i in range(n-1):
    connection_options = []
    for (frm, to) in allowed_flights:
        connection_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(connection_options))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:10s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")