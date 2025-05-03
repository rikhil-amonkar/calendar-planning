from z3 import *

# City indices and durations:
# 0: Krakow    (3 days)
# 1: Bucharest (2 days)
# 2: Berlin    (4 days) – Wedding in Berlin between day 3 and day 6 → force arrival = 3.
# 3: Munich    (4 days)
# 4: Santorini (5 days)
# 5: Athens    (3 days) – Meet friends in Athens between day 14 and day 16 → force arrival = 14.
# 6: Vienna    (5 days) – Workshop in Vienna between day 10 and day 14 → force arrival = 10.
#
# Total raw days = 3 + 2 + 4 + 4 + 5 + 3 + 5 = 26.
# There are 6 overlapping transit days between visits, so overall trip length = 26 - 6 = 20 days.

cities = ["Krakow", "Bucharest", "Berlin", "Munich", "Santorini", "Athens", "Vienna"]
durations = [3, 2, 4, 4, 5, 3, 5]

# Allowed direct flights (bidirectional, unless noted):
# 1. Berlin and Munich              -> (Berlin, Munich)           => (2, 3)
# 2. Bucharest and Vienna           -> (Bucharest, Vienna)        => (1, 6)
# 3. Berlin and Vienna              -> (Berlin, Vienna)           => (2, 6)
# 4. Vienna and Athens              -> (Vienna, Athens)           => (6, 5)
# 5. Vienna and Santorini           -> (Vienna, Santorini)        => (6, 4)
# 6. Munich and Bucharest           -> (Munich, Bucharest)        => (3, 1)
# 7. Berlin and Athens              -> (Berlin, Athens)           => (2, 5)
# 8. Bucharest and Athens           -> (Bucharest, Athens)        => (1, 5)
# 9. Krakow and Munich              -> (Krakow, Munich)           => (0, 3)
# 10. Munich and Vienna             -> (Munich, Vienna)           => (3, 6)
# 11. Krakow and Berlin             -> (Krakow, Berlin)           => (0, 2)
# 12. Bucharest and Santorini       -> (Bucharest, Santorini)     => (1, 4)
# 13. Munich and Athens             -> (Munich, Athens)           => (3, 5)
# 14. Athens and Santorini          -> (Athens, Santorini)        => (5, 4)
# 15. Krakow and Vienna             -> (Krakow, Vienna)           => (0, 6)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

add_bidirectional(2, 3)   # Berlin <-> Munich
add_bidirectional(1, 6)   # Bucharest <-> Vienna
add_bidirectional(2, 6)   # Berlin <-> Vienna
add_bidirectional(6, 5)   # Vienna <-> Athens
add_bidirectional(6, 4)   # Vienna <-> Santorini
add_bidirectional(3, 1)   # Munich <-> Bucharest
add_bidirectional(2, 5)   # Berlin <-> Athens
add_bidirectional(1, 5)   # Bucharest <-> Athens
add_bidirectional(0, 3)   # Krakow <-> Munich
add_bidirectional(3, 6)   # Munich <-> Vienna
add_bidirectional(0, 2)   # Krakow <-> Berlin
add_bidirectional(1, 4)   # Bucharest <-> Santorini
add_bidirectional(3, 5)   # Munich <-> Athens
add_bidirectional(5, 4)   # Athens <-> Santorini
add_bidirectional(0, 6)   # Krakow <-> Vienna

# Set up Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Permutation of visit order: order[i] is the city index visited in slot i.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Arrival and departure days for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit, if city c is visited then departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: Next arrival equals previous departure.
for i in range(n - 1):
    s.add(arrivals[i + 1] == departures[i])

# Overall trip must finish on day 20.
s.add(departures[n - 1] == 20)

# Event-specific constraints:
# Berlin (city index 2): Wedding between day 3 and 6 → force arrival = 3.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 3, True))

# Vienna (city index 6): Workshop between day 10 and 14 → force arrival = 10.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 10, True))
    
# Athens (city index 5): Meet friends between day 14 and 16 → force arrival = 14.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 14, True))

# Connectivity constraints: Each consecutive pair must have a direct flight.
for i in range(n - 1):
    possible_connections = []
    for (frm, to) in allowed_flights:
        possible_connections.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*possible_connections))

# Solve the model.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_idx]:10s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")