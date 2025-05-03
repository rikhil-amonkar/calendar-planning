from z3 import *

# Cities with durations and event constraints:
# 0: Valencia   (5 days) – Annual show from day 8 to day 12 → force arrival = 8.
# 1: Venice     (5 days)
# 2: Helsinki   (3 days)
# 3: Nice       (3 days)
# 4: Riga       (4 days) – Visit relatives from day 16 to day 19 → force arrival = 16.
# 5: Krakow     (3 days)
# 6: Stuttgart  (2 days)
#
# Total raw days = 5 + 5 + 3 + 3 + 4 + 3 + 2 = 25.
# With 6 overlapping transit days (between consecutive visits), overall trip length is 25 - 6 = 19 days.

cities = ["Valencia", "Venice", "Helsinki", "Nice", "Riga", "Krakow", "Stuttgart"]
durations = [5, 5, 3, 3, 4, 3, 2]

# Allowed direct flights (all bidirectional):
# 1. Stuttgart and Valencia
# 2. Valencia and Krakow
# 3. Krakow and Helsinki
# 4. Helsinki and Riga
# 5. Stuttgart and Krakow
# 6. Venice and Helsinki
# 7. Nice and Riga
# 8. Venice and Stuttgart
# 9. Nice and Helsinki
# 10. Nice and Venice

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Stuttgart <-> Valencia
bidir(6, 0)
# 2. Valencia <-> Krakow
bidir(0, 5)
# 3. Krakow <-> Helsinki
bidir(5, 2)
# 4. Helsinki <-> Riga
bidir(2, 4)
# 5. Stuttgart <-> Krakow
bidir(6, 5)
# 6. Venice <-> Helsinki
bidir(1, 2)
# 7. Nice <-> Riga
bidir(3, 4)
# 8. Venice <-> Stuttgart
bidir(1, 6)
# 9. Nice <-> Helsinki
bidir(3, 2)
# 10. Nice <-> Venice
bidir(3, 1)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define a permutation for the order of city visits.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit, the departure day is given by: arrival + duration - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: next city's arrival equals previous city's departure.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 19.
s.add(departures[n-1] == 19)

# Event-specific constraints:
# Valencia (city 0): must start on day 8 for the annual show.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 8, True))
# Riga (city 4): must start on day 16 to visit relatives.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 16, True))

# Connectivity constraints:
# Consecutive cities in the itinerary must be connected by a direct flight.
for i in range(n-1):
    connections = []
    for (frm, to) in allowed_flights:
        connections.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*connections))

# Solve the model and print the itinerary.
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