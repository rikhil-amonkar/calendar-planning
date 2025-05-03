from z3 import *

# City indices and durations:
# 0: Santorini  (2 days)
# 1: Venice     (3 days)
# 2: Seville    (2 days)
# 3: Athens     (3 days) – Annual show in Athens between day 2 and day 4 → force arrival = 2.
# 4: Amsterdam  (2 days)
# 5: Stockholm  (2 days)
# 6: Stuttgart  (2 days) – Wedding in Stuttgart between day 1 and day 2 → force arrival = 1.
#
# Total raw days = 2 + 3 + 2 + 3 + 2 + 2 + 2 = 16.
# With 6 overlapping transit days (the end of one visit is the start of the next),
# overall trip length = 16 - 6 = 10 days.

cities = ["Santorini", "Venice", "Seville", "Athens", "Amsterdam", "Stockholm", "Stuttgart"]
durations = [2, 3, 2, 3, 2, 2, 2]

# Allowed direct flights:
# Note: All flights are bidirectional except the one specified as "from Stockholm to Santorini".
# 1. From Stockholm to Santorini: one-way (Stockholm, Santorini) -> (5, 0)
# 2. Athens and Amsterdam: bidirectional (3,4) and (4,3)
# 3. Stuttgart and Stockholm: bidirectional (6,5) and (5,6)
# 4. Stockholm and Amsterdam: bidirectional (5,4) and (4,5)
# 5. Athens and Venice: bidirectional (3,1) and (1,3)
# 6. Athens and Stockholm: bidirectional (3,5) and (5,3)
# 7. Athens and Santorini: bidirectional (3,0) and (0,3)
# 8. Santorini and Venice: bidirectional (0,1) and (1,0)
# 9. Amsterdam and Seville: bidirectional (4,2) and (2,4)
# 10. Stuttgart and Athens: bidirectional (6,3) and (3,6)
# 11. Stuttgart and Venice: bidirectional (6,1) and (1,6)
# 12. Stuttgart and Amsterdam: bidirectional (6,4) and (4,6)
# 13. Santorini and Amsterdam: bidirectional (0,4) and (4,0)
# 14. Venice and Amsterdam: bidirectional (1,4) and (4,1)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. One-way: Stockholm -> Santorini
allowed_flights.append((5, 0))

# 2.
add_bidirectional(3, 4)   # Athens <-> Amsterdam
# 3.
add_bidirectional(6, 5)   # Stuttgart <-> Stockholm
# 4.
add_bidirectional(5, 4)   # Stockholm <-> Amsterdam
# 5.
add_bidirectional(3, 1)   # Athens <-> Venice
# 6.
add_bidirectional(3, 5)   # Athens <-> Stockholm
# 7.
add_bidirectional(3, 0)   # Athens <-> Santorini
# 8.
add_bidirectional(0, 1)   # Santorini <-> Venice
# 9.
add_bidirectional(4, 2)   # Amsterdam <-> Seville
# 10.
add_bidirectional(6, 3)   # Stuttgart <-> Athens
# 11.
add_bidirectional(6, 1)   # Stuttgart <-> Venice
# 12.
add_bidirectional(6, 4)   # Stuttgart <-> Amsterdam
# 13.
add_bidirectional(0, 4)   # Santorini <-> Amsterdam
# 14.
add_bidirectional(1, 4)   # Venice <-> Amsterdam

# Set up the Z3 solver
s = Solver()
n = len(cities)  # 7 cities

# The order in which cities are visited (a permutation of [0..6])
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Define arrival and departure day variables for each visit
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1
s.add(arrivals[0] == 1)

# For each visit i, if city c is visited then:
# departure[i] = arrival[i] + durations[c] - 1
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: The next visit starts on the same day the previous visit ends.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 10.
s.add(departures[n-1] == 10)

# Event-specific constraints:
# Stuttgart (city index 6): wedding between day1 and day2 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 1, True))
# Athens (city index 3): annual show between day2 and day4 → force arrival = 2.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 2, True))

# Connectivity constraints:
# Each consecutive pair of visited cities must have a direct flight connection.
for i in range(n - 1):
    possible_flights = []
    for (frm, to) in allowed_flights:
        possible_flights.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*possible_flights))

# Solve and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_i = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_i]:12s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")