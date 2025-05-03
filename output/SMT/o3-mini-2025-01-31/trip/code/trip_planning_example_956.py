from z3 import *

# Define the 7 cities with durations and event constraints:
# 0: Venice     (3 days) – Workshop in Venice between day 13 and day 15 ⇒ force arrival = 13.
# 1: Warsaw     (5 days)
# 2: Santorini  (2 days) – Conference in Santorini during day 15 and 16 ⇒ force arrival = 15.
# 3: Madrid     (3 days)
# 4: Reykjavik  (5 days)
# 5: Budapest   (2 days)
# 6: Florence   (2 days) – Annual show in Florence from day 1 to day 2 ⇒ force arrival = 1.
#
# Total raw days = 3 + 5 + 2 + 3 + 5 + 2 + 2 = 22.
# With 6 transitions (each consecutive visit shares one day) the overall trip lasts:
#   22 - 6 = 16 days.
cities = ["Venice", "Warsaw", "Santorini", "Madrid", "Reykjavik", "Budapest", "Florence"]
durations = [3, 5, 2, 3, 5, 2, 2]

# Allowed direct flights:
# 1. Madrid and Santorini          -> bidir (Madrid, Santorini): (3, 2)
# 2. Reykjavik and Warsaw           -> bidir (Reykjavik, Warsaw): (4, 1)
# 3. from Reykjavik to Madrid       -> one-way: (Reykjavik -> Madrid): (4, 3)
# 4. Budapest and Warsaw            -> bidir (Budapest, Warsaw): (5, 1)
# 5. Venice and Santorini           -> bidir (Venice, Santorini): (0, 2)
# 6. Madrid and Venice              -> bidir (Madrid, Venice): (3, 0)
# 7. Madrid and Budapest            -> bidir (Madrid, Budapest): (3, 5)
# 8. Florence and Madrid            -> bidir (Florence, Madrid): (6, 3)
# 9. Madrid and Warsaw              -> bidir (Madrid, Warsaw): (3, 1)
# 10. Budapest and Reykjavik        -> bidir (Budapest, Reykjavik): (5, 4)
# 11. Warsaw and Venice             -> bidir (Warsaw, Venice): (1, 0)

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

bidir(3, 2)  # Madrid <-> Santorini
bidir(4, 1)  # Reykjavik <-> Warsaw
# One-way flight: from Reykjavik (4) to Madrid (3)
allowed_flights.append((4, 3))
bidir(5, 1)  # Budapest <-> Warsaw
bidir(0, 2)  # Venice <-> Santorini
bidir(3, 0)  # Madrid <-> Venice
bidir(3, 5)  # Madrid <-> Budapest
bidir(6, 3)  # Florence <-> Madrid
bidir(3, 1)  # Madrid <-> Warsaw
bidir(5, 4)  # Budapest <-> Reykjavik
bidir(1, 0)  # Warsaw <-> Venice

# Set up the Z3 solver.
s = Solver()
n = len(cities)

# Define the visitation order as a permutation of city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables per visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit, departure = arrival + duration - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share a transit day.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 16.
s.add(departures[n-1] == 16)

# Event-specific constraints:
# Venice (city 0): workshop between day 13 and 15, force arrival = 13.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 13, True))
# Santorini (city 2): conference during day 15 and 16, force arrival = 15.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 15, True))
# Florence (city 6): annual show from day 1 to day 2, force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 1, True))

# Connectivity constraints:
# For every pair of consecutive cities, there must be a direct flight from the earlier to the later city.
for i in range(n-1):
    flight_options = []
    for (frm, to) in allowed_flights:
        flight_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*flight_options))

# Solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_idx]:10s}: [{a_day}, {d_day}]")
else:
    print("No solution found")