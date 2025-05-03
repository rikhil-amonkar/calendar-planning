from z3 import *

# Cities with indices, durations and event constraints:
# 0: Porto    (5 days)
# 1: Lyon     (3 days)
# 2: Krakow   (4 days)
# 3: Naples   (2 days)
# 4: Hamburg  (4 days)
# 5: Warsaw   (2 days) – Conference in Warsaw between day 4 and day 5 ⇒ force arrival = 4.
# 6: Budapest (5 days) – Wedding in Budapest between day 6 and day 10 ⇒ force arrival = 6.
#
# Total raw days = 5 + 3 + 4 + 2 + 4 + 2 + 5 = 25.
# With 6 transitions (overlap of one day each), overall trip length = 25 - 6 = 19 days.

cities = ["Porto", "Lyon", "Krakow", "Naples", "Hamburg", "Warsaw", "Budapest"]
durations = [5, 3, 4, 2, 4, 2, 5]

# Allowed direct flights (assumed bidirectional):
# 1. Warsaw and Porto
# 2. Budapest and Hamburg
# 3. Warsaw and Naples
# 4. Hamburg and Porto
# 5. Krakow and Warsaw
# 6. Warsaw and Budapest
# 7. Naples and Budapest
# 8. Porto and Lyon
# 9. Warsaw and Hamburg

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Warsaw <-> Porto
bidir(5, 0)
# 2. Budapest <-> Hamburg
bidir(6, 4)
# 3. Warsaw <-> Naples
bidir(5, 3)
# 4. Hamburg <-> Porto
bidir(4, 0)
# 5. Krakow <-> Warsaw
bidir(2, 5)
# 6. Warsaw <-> Budapest
bidir(5, 6)
# 7. Naples <-> Budapest
bidir(3, 6)
# 8. Porto <-> Lyon
bidir(0, 1)
# 9. Warsaw <-> Hamburg
bidir(5, 4)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the order in which the cities are visited (a permutation of 0..6).
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visitation slot, the departure is calculated as:
#    departure = arrival + duration - 1
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share a transit day.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 19.
s.add(departures[n-1] == 19)

# Event-specific constraints:
# Warsaw (city 5): conference between day 4 and day 5 → force arrival = 4.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 4, True))
# Budapest (city 6): wedding between day 6 and day 10 → force arrival = 6.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 6, True))

# Connectivity constraints:
# Each consecutive pair of cities must be connected by a direct flight.
for i in range(n-1):
    possible_flights = []
    for (frm, to) in allowed_flights:
        possible_flights.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*possible_flights))

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