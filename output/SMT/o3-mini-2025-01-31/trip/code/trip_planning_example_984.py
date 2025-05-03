from z3 import *

# City indices and durations:
# 0: Oslo      (5 days) – Meet a friend in Oslo between day 8 and 12 → force arrival = 8.
# 1: Bucharest (3 days)
# 2: Stuttgart (3 days) – Conference in Stuttgart between day 5 and 7 → force arrival = 5.
# 3: Istanbul (2 days)
# 4: Brussels (2 days)
# 5: Santorini(2 days)
# 6: Stockholm(2 days)

# Total raw days = 5 + 3 + 3 + 2 + 2 + 2 + 2 = 19.
# With 6 transitions (overlap days) the overall trip length is 19 - 6 = 13 days.
cities = ["Oslo", "Bucharest", "Stuttgart", "Istanbul", "Brussels", "Santorini", "Stockholm"]
durations = [5, 3, 3, 2, 2, 2, 2]

# Allowed direct flights:
allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Stockholm and Brussels: (Stockholm=6, Brussels=4)
add_bidirectional(6, 4)
# 2. Istanbul and Brussels: (Istanbul=3, Brussels=4)
add_bidirectional(3, 4)
# 3. Stuttgart and Stockholm: (Stuttgart=2, Stockholm=6)
add_bidirectional(2, 6)
# 4. Istanbul and Stockholm: (Istanbul=3, Stockholm=6)
add_bidirectional(3, 6)
# 5. Bucharest and Brussels: (Bucharest=1, Brussels=4)
add_bidirectional(1, 4)
# 6. from Santorini to Oslo: one-way from Santorini (5) to Oslo (0)
allowed_flights.append((5, 0))
# 7. Stockholm and Oslo: (Stockholm=6, Oslo=0)
add_bidirectional(6, 0)
# 8. Bucharest and Oslo: (Bucharest=1, Oslo=0)
add_bidirectional(1, 0)
# 9. Santorini and Bucharest: (Santorini=5, Bucharest=1)
add_bidirectional(5, 1)
# 10. Bucharest and Istanbul: (Bucharest=1, Istanbul=3)
add_bidirectional(1, 3)
# 11. Istanbul and Oslo: (Istanbul=3, Oslo=0)
add_bidirectional(3, 0)
# 12. Oslo and Brussels: (Oslo=0, Brussels=4)
add_bidirectional(0, 4)
# 13. from Stockholm to Santorini: one-way from Stockholm (6) to Santorini (5)
allowed_flights.append((6, 5))
# 14. Istanbul and Stuttgart: (Istanbul=3, Stuttgart=2)
add_bidirectional(3, 2)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# The itinerary order as a permutation of cities.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Arrival and departure times for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit time slot i, if the city c is visited then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: next visit's arrival equals previous visit's departure.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 13.
s.add(departures[n-1] == 13)

# Event-specific constraints:
# Oslo (index 0): meet a friend between day 8 and day 12 → force arrival = 8.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 8, True))
# Stuttgart (index 2): conference between day 5 and day 7 → force arrival = 5.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 5, True))

# Connectivity constraints: 
# Each consecutive pair of cities must be linked by a direct flight.
for i in range(n - 1):
    flight_options = []
    for (frm, to) in allowed_flights:
        flight_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(flight_options))

# Solve the model and print the itinerary.
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