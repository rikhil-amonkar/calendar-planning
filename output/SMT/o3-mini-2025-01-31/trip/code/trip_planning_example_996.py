from z3 import *

# City indices and durations:
# 0: Valencia  (5 days)
# 1: Riga      (5 days)
# 2: Prague    (3 days) – Relatives event between day 7 and 9, so force arrival = 7.
# 3: Mykonos   (3 days) – Wedding between day 1 and 3, so force arrival = 1.
# 4: Zurich    (5 days)
# 5: Bucharest (5 days)
# 6: Nice      (2 days)
#
# Total raw days = 5 + 5 + 3 + 3 + 5 + 5 + 2 = 28.
# There are 6 overlaps between 7 cities, so overall trip length = 28 - 6 = 22 days.

cities = ["Valencia", "Riga", "Prague", "Mykonos", "Zurich", "Bucharest", "Nice"]
durations = [5, 5, 3, 3, 5, 5, 2]

# Allowed direct flights (all bidirectional unless noted otherwise):
# 1. Mykonos and Nice
# 2. Mykonos and Zurich
# 3. Prague and Bucharest
# 4. Valencia and Bucharest
# 5. Zurich and Prague
# 6. Riga and Nice
# 7. Zurich and Riga
# 8. Zurich and Bucharest
# 9. Zurich and Valencia
# 10. Bucharest and Riga
# 11. Prague and Riga
# 12. Prague and Valencia
# 13. Zurich and Nice

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Mykonos <-> Nice
add_bidirectional(3, 6)
# 2. Mykonos <-> Zurich
add_bidirectional(3, 4)
# 3. Prague <-> Bucharest
add_bidirectional(2, 5)
# 4. Valencia <-> Bucharest
add_bidirectional(0, 5)
# 5. Zurich <-> Prague
add_bidirectional(4, 2)
# 6. Riga <-> Nice
add_bidirectional(1, 6)
# 7. Zurich <-> Riga
add_bidirectional(4, 1)
# 8. Zurich <-> Bucharest
add_bidirectional(4, 5)
# 9. Zurich <-> Valencia
add_bidirectional(4, 0)
# 10. Bucharest <-> Riga
add_bidirectional(5, 1)
# 11. Prague <-> Riga
add_bidirectional(2, 1)
# 12. Prague <-> Valencia
add_bidirectional(2, 0)
# 13. Zurich <-> Nice
add_bidirectional(4, 6)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# We represent the itinerary as a permutation of the 7 cities.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Define arrival and departure day variables for each visit in the itinerary.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot, if city c is assigned to that slot then its departure = arrival + duration[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: the arrival of the next equals the departure of the previous.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 22.
s.add(departures[n-1] == 22)

# Event-specific constraints:
# Prague (index 2): Visit relatives between day 7 and 9, so force arrival = 7.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 7, True))
# Mykonos (index 3): Wedding between day 1 and 3, so force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 1, True))

# Connectivity constraints:
# For each consecutive pair of visits in the itinerary, there must be a direct flight.
for i in range(n - 1):
    s.add(Or([And(order[i] == frm, order[i+1] == to) for (frm, to) in allowed_flights]))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city = cities[m.evaluate(order[i]).as_long()]
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {city:10s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")