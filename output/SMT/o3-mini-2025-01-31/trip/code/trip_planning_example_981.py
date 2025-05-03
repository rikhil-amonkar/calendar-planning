from z3 import *

# City indices and durations:
# 0: Tallinn   (5 days)
# 1: Paris     (3 days)  – Workshop in Paris between day 8 and 10 → force arrival = 8.
# 2: Vienna    (4 days)  – Annual show in Vienna from day 5 to 8 → force arrival = 5.
# 3: Santorini (5 days)
# 4: Stuttgart (2 days)  – Visit relatives in Stuttgart between day 13 and 14 → force arrival = 13.
# 5: Warsaw    (3 days)
# 6: Valencia  (4 days)

# Total raw days = 5 + 3 + 4 + 5 + 2 + 3 + 4 = 26 days.
# With 6 overlapping transit days (when moving between 7 cities),
# overall trip length = 26 - 6 = 20 days.

cities = ["Tallinn", "Paris", "Vienna", "Santorini", "Stuttgart", "Warsaw", "Valencia"]
durations = [5, 3, 4, 5, 2, 3, 4]

# Allowed direct flights (all bidirectional unless noted otherwise):
# 1. Santorini and Vienna      -> (Santorini, Vienna): (3,2)
# 2. Paris and Stuttgart        -> (Paris, Stuttgart): (1,4)
# 3. Valencia and Warsaw        -> (Valencia, Warsaw): (6,5)
# 4. Vienna and Warsaw          -> (Vienna, Warsaw): (2,5)
# 5. Vienna and Stuttgart       -> (Vienna, Stuttgart): (2,4)
# 6. Valencia and Stuttgart     -> (Valencia, Stuttgart): (6,4)
# 7. Warsaw and Tallinn         -> (Warsaw, Tallinn): (5,0)
# 8. Vienna and Valencia        -> (Vienna, Valencia): (2,6)
# 9. Stuttgart and Warsaw       -> (Stuttgart, Warsaw): (4,5)
# 10. Vienna and Paris          -> (Vienna, Paris): (2,1)
# 11. Paris and Warsaw          -> (Paris, Warsaw): (1,5)
# 12. Paris and Tallinn         -> (Paris, Tallinn): (1,0)
# 13. Paris and Valencia        -> (Paris, Valencia): (1,6)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

add_bidirectional(3, 2)  # Santorini <-> Vienna
add_bidirectional(1, 4)  # Paris <-> Stuttgart
add_bidirectional(6, 5)  # Valencia <-> Warsaw
add_bidirectional(2, 5)  # Vienna <-> Warsaw
add_bidirectional(2, 4)  # Vienna <-> Stuttgart
add_bidirectional(6, 4)  # Valencia <-> Stuttgart
add_bidirectional(5, 0)  # Warsaw <-> Tallinn
add_bidirectional(2, 6)  # Vienna <-> Valencia
add_bidirectional(4, 5)  # Stuttgart <-> Warsaw
add_bidirectional(2, 1)  # Vienna <-> Paris
add_bidirectional(1, 5)  # Paris <-> Warsaw
add_bidirectional(1, 0)  # Paris <-> Tallinn
add_bidirectional(1, 6)  # Paris <-> Valencia

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

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if city c is visited then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    city_constraints = []
    for c in range(n):
        city_constraints.append(If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False))
    s.add(Or(city_constraints))

# Consecutive visits: the next visit starts on the day the previous visit ends.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 20.
s.add(departures[n-1] == 20)

# Event-specific constraints:
# Paris (index 1): workshop between day 8 and day 10 → force arrival = 8.
for i in range(n):
    s.add(If(order[i] == 1, arrivals[i] == 8, True))
# Vienna (index 2): annual show from day 5 to day 8 → force arrival = 5.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 5, True))
# Stuttgart (index 4): visit relatives between day 13 and day 14 → force arrival = 13.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 13, True))

# Connectivity constraints:
# Each consecutive pair of visited cities must be connected by an allowed direct flight.
for i in range(n-1):
    connections = []
    for (frm, to) in allowed_flights:
        connections.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(connections))

# Solve and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        c_idx = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[c_idx]:10s}: [{a_day}, {d_day}]")
else:
    print("No solution found")