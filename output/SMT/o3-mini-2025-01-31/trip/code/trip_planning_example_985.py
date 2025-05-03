from z3 import *

# City indices and durations:
# 0: Bucharest (3 days)
# 1: Geneva    (2 days) – Wedding in Geneva between day 2 and 3 → force arrival = 2.
# 2: Tallinn   (4 days)
# 3: Naples    (2 days) – Meet friend in Naples between day 1 and 2 → force arrival = 1.
# 4: Valencia  (3 days)
# 5: Porto     (4 days)
# 6: Brussels  (4 days)
#
# Total raw days = 3 + 2 + 4 + 2 + 3 + 4 + 4 = 22.
# There are 6 overlaps when transitioning between 7 cities, so overall trip length = 22 - 6 = 16 days.

cities = ["Bucharest", "Geneva", "Tallinn", "Naples", "Valencia", "Porto", "Brussels"]
durations = [3, 2, 4, 2, 3, 4, 4]

# Allowed direct flights (bidirectional):
# - Naples and Bucharest: (3,0)
# - Geneva and Porto: (1,5)
# - Bucharest and Brussels: (0,6)
# - Naples and Brussels: (3,6)
# - Naples and Valencia: (3,4)
# - Porto and Valencia: (5,4)
# - Brussels and Tallinn: (6,2)
# - Geneva and Valencia: (1,4)
# - Geneva and Brussels: (1,6)
# - Valencia and Bucharest: (4,0)
# - Naples and Geneva: (3,1)
# - Valencia and Brussels: (4,6)
# - Porto and Brussels: (5,6)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

add_bidirectional(3, 0)  # Naples <-> Bucharest
add_bidirectional(1, 5)  # Geneva <-> Porto
add_bidirectional(0, 6)  # Bucharest <-> Brussels
add_bidirectional(3, 6)  # Naples <-> Brussels
add_bidirectional(3, 4)  # Naples <-> Valencia
add_bidirectional(5, 4)  # Porto <-> Valencia
add_bidirectional(6, 2)  # Brussels <-> Tallinn
add_bidirectional(1, 4)  # Geneva <-> Valencia
add_bidirectional(1, 6)  # Geneva <-> Brussels
add_bidirectional(4, 0)  # Valencia <-> Bucharest
add_bidirectional(3, 1)  # Naples <-> Geneva
add_bidirectional(4, 6)  # Valencia <-> Brussels
add_bidirectional(5, 6)  # Porto <-> Brussels

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the visit order as a permutation of city indices.
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
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: the arrival day of the next city equals the departure day of the previous visit.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 16.
s.add(departures[n-1] == 16)

# Event-specific constraints:
# Geneva (index 1): Wedding between day 2 and 3 → force arrival = 2.
for i in range(n):
    s.add(If(order[i] == 1, arrivals[i] == 2, True))
# Naples (index 3): Meet friend between day 1 and 2 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 1, True))

# Connectivity: each consecutive pair of cities in the itinerary must be connected by a direct flight.
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