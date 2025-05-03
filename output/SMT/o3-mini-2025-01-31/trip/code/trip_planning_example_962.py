from z3 import *

# Cities with durations and event constraints:
# 0: Lyon       (3 days)
# 1: Split      (5 days) – Wedding in Split between day 3 and day 7 ⇒ force arrival = 3.
# 2: Mykonos    (2 days)
# 3: Reykjavik  (3 days)
# 4: Stuttgart  (4 days) – Meet friends in Stuttgart between day 11 and day 14 ⇒ force arrival = 11.
# 5: Copenhagen (3 days)
# 6: Amsterdam  (3 days)
#
# Total raw days = 3 + 5 + 2 + 3 + 4 + 3 + 3 = 23.
# With 6 transitions (overlap of one day each between consecutive visits),
# overall trip length = 23 - 6 = 17 days.
cities = ["Lyon", "Split", "Mykonos", "Reykjavik", "Stuttgart", "Copenhagen", "Amsterdam"]
durations = [3, 5, 2, 3, 4, 3, 3]

# Allowed direct flights:
# 1. Split and Stuttgart          -> bidirectional between (Split, Stuttgart)         => (1,4)
# 2. Lyon and Split              -> bidirectional between (Lyon, Split)              => (0,1)
# 3. from Reykjavik to Stuttgart -> one-way from (Reykjavik, Stuttgart)             => (3,4)
# 4. Reykjavik and Amsterdam      -> bidirectional between (Reykjavik, Amsterdam)      => (3,6)
# 5. Split and Copenhagen         -> bidirectional between (Split, Copenhagen)         => (1,5)
# 6. Amsterdam and Mykonos        -> bidirectional between (Amsterdam, Mykonos)        => (6,2)
# 7. Copenhagen and Stuttgart     -> bidirectional between (Copenhagen, Stuttgart)     => (5,4)
# 8. Stuttgart and Amsterdam      -> bidirectional between (Stuttgart, Amsterdam)      => (4,6)
# 9. Split and Amsterdam          -> bidirectional between (Split, Amsterdam)          => (1,6)
# 10. Lyon and Amsterdam          -> bidirectional between (Lyon, Amsterdam)           => (0,6)
# 11. Copenhagen and Reykjavik    -> bidirectional between (Copenhagen, Reykjavik)     => (5,3)
# 12. Copenhagen and Amsterdam    -> bidirectional between (Copenhagen, Amsterdam)     => (5,6)

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# Flight 1: Split <-> Stuttgart
bidir(1, 4)
# Flight 2: Lyon <-> Split
bidir(0, 1)
# Flight 3: One-way: from Reykjavik to Stuttgart
allowed_flights.append((3, 4))
# Flight 4: Reykjavik <-> Amsterdam
bidir(3, 6)
# Flight 5: Split <-> Copenhagen
bidir(1, 5)
# Flight 6: Amsterdam <-> Mykonos
bidir(6, 2)
# Flight 7: Copenhagen <-> Stuttgart
bidir(5, 4)
# Flight 8: Stuttgart <-> Amsterdam
bidir(4, 6)
# Flight 9: Split <-> Amsterdam
bidir(1, 6)
# Flight 10: Lyon <-> Amsterdam
bidir(0, 6)
# Flight 11: Copenhagen <-> Reykjavik
bidir(5, 3)
# Flight 12: Copenhagen <-> Amsterdam
bidir(5, 6)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Permutation: Define the visitation order as a permutation of indices 0..6.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# Each visit's departure is computed as: departure = arrival + duration - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: the next city’s arrival equals the previous city’s departure.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 17.
s.add(departures[n-1] == 17)

# Event constraints:
# Split (city 1): Wedding between day 3 and 7 -> force arrival = 3.
for i in range(n):
    s.add(If(order[i] == 1, arrivals[i] == 3, True))
# Stuttgart (city 4): Meet friends between day 11 and 14 -> force arrival = 11.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 11, True))

# Connectivity: Each consecutive pair must be connected by a direct flight.
for i in range(n - 1):
    connection_possible = []
    for (frm, to) in allowed_flights:
        connection_possible.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*connection_possible))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_idx]:11s}: [{a_day}, {d_day}]")
else:
    print("No solution found")