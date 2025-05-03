from z3 import *

# Cities (with indices and durations):
# 0: Munich    (4 days)
# 1: London    (2 days) – Meet a friend between day 19 and day 20 ⇒ force arrival = 19.
# 2: Venice    (5 days) – Visit relatives between day 8 and day 12 ⇒ force arrival = 8.
# 3: Split     (4 days)
# 4: Geneva    (2 days)
# 5: Zurich    (5 days) – Attend a conference during day 15 to day 19 ⇒ force arrival = 15.
# 6: Lyon      (5 days)
#
# Total raw days = 4 + 2 + 5 + 4 + 2 + 5 + 5 = 27.
# With 6 transitions (each consecutive visit shares one day), overall trip length = 27 - 6 = 21 days.
cities = ["Munich", "London", "Venice", "Split", "Geneva", "Zurich", "Lyon"]
durations = [4, 2, 5, 4, 2, 5, 5]

# Allowed direct flights (bidirectional):
# 1. Munich and Geneva      → (0, 4)
# 2. Zurich and Geneva      → (5, 4)
# 3. Split and Lyon         → (3, 6)
# 4. Zurich and London      → (5, 1)
# 5. London and Geneva      → (1, 4)
# 6. Venice and London      → (2, 1)
# 7. Munich and London      → (0, 1)
# 8. Split and London       → (3, 1)
# 9. Munich and Zurich      → (0, 5)
# 10. Lyon and Munich       → (6, 0)
# 11. Split and Zurich      → (3, 5)
# 12. Lyon and Venice       → (6, 2)
# 13. Venice and Munich      → (2, 0)
# 14. Venice and Zurich      → (2, 5)
# 15. Split and Geneva      → (3, 4)
# 16. Split and Munich      → (3, 0)
# 17. Lyon and London       → (6, 1)

allowed_flights = []
def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

bidir(0, 4)  # Munich <-> Geneva
bidir(5, 4)  # Zurich <-> Geneva
bidir(3, 6)  # Split <-> Lyon
bidir(5, 1)  # Zurich <-> London
bidir(1, 4)  # London <-> Geneva
bidir(2, 1)  # Venice <-> London
bidir(0, 1)  # Munich <-> London
bidir(3, 1)  # Split <-> London
bidir(0, 5)  # Munich <-> Zurich
bidir(6, 0)  # Lyon <-> Munich
bidir(3, 5)  # Split <-> Zurich
bidir(6, 2)  # Lyon <-> Venice
bidir(2, 0)  # Venice <-> Munich
bidir(2, 5)  # Venice <-> Zurich
bidir(3, 4)  # Split <-> Geneva
bidir(3, 0)  # Split <-> Munich
bidir(6, 1)  # Lyon <-> London

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the visitation order as a permutation of the city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each city visit in the order.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, departure day = arrival day + duration - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day:
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 21.
s.add(departures[n-1] == 21)

# Event-specific constraints:
# London (city 1): meet a friend between day 19 and day 20, so force arrival = 19.
for i in range(n):
    s.add(If(order[i] == 1, arrivals[i] == 19, True))
# Venice (city 2): visit relatives between day 8 and day 12, so force arrival = 8.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 8, True))
# Zurich (city 5): attend a conference during day 15 to day 19, so force arrival = 15.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 15, True))

# Connectivity constraints:
# For every consecutive pair in the itinerary, there must be a direct flight.
for i in range(n - 1):
    flight_options = []
    for (frm, to) in allowed_flights:
        flight_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*flight_options))

# Solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:8s}: [{a_day}, {d_day}]")
else:
    print("No solution found")