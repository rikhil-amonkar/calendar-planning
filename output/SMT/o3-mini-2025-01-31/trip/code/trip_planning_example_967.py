from z3 import *

# Cities with durations and event constraints:
# 0: Budapest   (2 days) – Conference from day 7 to day 8 ⇒ force arrival = 7.
# 1: Mykonos    (3 days)
# 2: Lyon       (4 days) – Meet friend between day 1 and day 4 ⇒ force arrival = 1.
# 3: Reykjavik  (2 days) – Annual show from day6 to day7 ⇒ force arrival = 6.
# 4: Lisbon     (3 days)
# 5: Athens     (4 days)
# 6: Riga       (2 days)
#
# The raw sum of durations = 2 + 3 + 4 + 2 + 3 + 4 + 2 = 20 days.
# With 6 overlaps (transit days) the overall trip length = 20 - 6 = 14 days.

cities = ["Budapest", "Mykonos", "Lyon", "Reykjavik", "Lisbon", "Athens", "Riga"]
durations = [2, 3, 4, 2, 3, 4, 2]

# Allowed direct flights (using city indices):
# 1. Lisbon and Reykjavik         -> bidirectional: (Lisbon, Reykjavik) => (4, 3)
# 2. from Athens to Riga           -> one-way: (Athens, Riga) => (5, 6)
# 3. Lisbon and Riga              -> bidirectional: (Lisbon, Riga) => (4, 6)
# 4. Mykonos and Athens           -> bidirectional: (Mykonos, Athens) => (1, 5)
# 5. Lisbon and Athens            -> bidirectional: (Lisbon, Athens) => (4, 5)
# 6. from Reykjavik to Athens     -> one-way: (Reykjavik, Athens) => (3, 5)
# 7. Lyon and Lisbon              -> bidirectional: (Lyon, Lisbon) => (2, 4)
# 8. Lisbon and Budapest          -> bidirectional: (Lisbon, Budapest) => (4, 0)
# 9. Reykjavik and Budapest       -> bidirectional: (Reykjavik, Budapest) => (3, 0)
# 10. Budapest and Mykonos        -> bidirectional: (Budapest, Mykonos) => (0, 1)

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Lisbon <-> Reykjavik
bidir(4, 3)
# 2. One-way: Athens -> Riga
allowed_flights.append((5, 6))
# 3. Lisbon <-> Riga
bidir(4, 6)
# 4. Mykonos <-> Athens
bidir(1, 5)
# 5. Lisbon <-> Athens
bidir(4, 5)
# 6. One-way: Reykjavik -> Athens
allowed_flights.append((3, 5))
# 7. Lyon <-> Lisbon
bidir(2, 4)
# 8. Lisbon <-> Budapest
bidir(4, 0)
# 9. Reykjavik <-> Budapest
bidir(3, 0)
# 10. Budapest <-> Mykonos
bidir(0, 1)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the visitation order as a permutation of {0,...,6}
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit, departure = arrival + (duration - 1)
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: The next visit starts when the previous ends.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])
    
# Overall trip must finish on day 14.
s.add(departures[n-1] == 14)

# Event specific constraints:
# Budapest (city index 0): conference on day 7-8, force arrival = 7.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 7, True))
# Lyon (city index 2): meet friend between day 1 and day 4, force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 1, True))
# Reykjavik (city index 3): annual show from day 6 to day 7, force arrival = 6.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 6, True))

# Connectivity constraints:
# Each consecutive pair of visits must have a direct flight.
for i in range(n - 1):
    possible = []
    for (frm, to) in allowed_flights:
        possible.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*possible))

# Solve and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city]:10s}: [{a_day}, {d_day}]")
else:
    print("No solution found")