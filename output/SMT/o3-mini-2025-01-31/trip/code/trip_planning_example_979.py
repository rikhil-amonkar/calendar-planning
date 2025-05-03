from z3 import *

# City indices and durations:
# 0: Santorini (2 days) – Wedding in Santorini between day 5 and 6 → force arrival = 5.
# 1: Mykonos   (4 days)
# 2: Lyon      (5 days)
# 3: Naples    (2 days)
# 4: Rome      (5 days) – Annual show in Rome between day 6 and 10 → force arrival = 6.
# 5: Vilnius   (3 days)
# 6: Istanbul  (3 days)
#
# Total raw days = 2 + 4 + 5 + 2 + 5 + 3 + 3 = 24. There are 6 overlapping transit days,
# so overall trip length = 24 - 6 = 18 days.

cities = ["Santorini", "Mykonos", "Lyon", "Naples", "Rome", "Vilnius", "Istanbul"]
durations = [2, 4, 5, 2, 5, 3, 3]

# Allowed direct flights (using city index):
# 1. Rome and Lyon              -> bidirectional: (Rome, Lyon)         => (4,2)
# 2. Naples and Rome            -> bidirectional: (Naples, Rome)       => (3,4)
# 3. Rome and Istanbul          -> bidirectional: (Rome, Istanbul)     => (4,6)
# 4. Santorini and Rome         -> bidirectional: (Santorini, Rome)    => (0,4)
# 5. Mykonos and Naples         -> bidirectional: (Mykonos, Naples)    => (1,3)
# 6. Lyon and Istanbul          -> bidirectional: (Lyon, Istanbul)     => (2,6)
# 7. Mykonos and Rome           -> bidirectional: (Mykonos, Rome)      => (1,4)
# 8. Naples and Santorini       -> bidirectional: (Naples, Santorini)  => (3,0)
# 9. Istanbul and Vilnius       -> bidirectional: (Istanbul, Vilnius)  => (6,5)
# 10. Naples and Istanbul       -> bidirectional: (Naples, Istanbul)   => (3,6)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

add_bidirectional(4, 2)   # Rome <-> Lyon
add_bidirectional(3, 4)   # Naples <-> Rome
add_bidirectional(4, 6)   # Rome <-> Istanbul
add_bidirectional(0, 4)   # Santorini <-> Rome
add_bidirectional(1, 3)   # Mykonos <-> Naples
add_bidirectional(2, 6)   # Lyon <-> Istanbul
add_bidirectional(1, 4)   # Mykonos <-> Rome
add_bidirectional(3, 0)   # Naples <-> Santorini
add_bidirectional(6, 5)   # Istanbul <-> Vilnius
add_bidirectional(3, 6)   # Naples <-> Istanbul

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the visit order as a permutation of the city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Define arrival and departure days for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the city c occupies that slot, then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: the next visit's arrival is the same as the previous visit's departure.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 18.
s.add(departures[n-1] == 18)

# Event-specific constraints:
# Santorini (city index 0): Wedding between day 5 and 6 → force arrival = 5.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 5, True))
# Rome (city index 4): Annual show from day 6 to 10 → force arrival = 6.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 6, True))

# Connectivity constraints:
# Each consecutive pair of visited cities must be connected by an allowed direct flight.
for i in range(n-1):
    connection_options = []
    for (frm, to) in allowed_flights:
        connection_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*connection_options))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        arrive = m.evaluate(arrivals[i]).as_long()
        depart = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:12s}: [{arrive}, {depart}]")
else:
    print("No solution found")