from z3 import *

# Cities:
# 0: Munich    (3 days) – Meet a friend in Munich between day 9 and day 11, force arrival = 9.
# 1: Hamburg   (4 days)
# 2: Lyon      (3 days)
# 3: Stockholm (5 days)
# 4: Berlin    (3 days) – Attend a workshop in Berlin between day 7 and day 9, force arrival = 7.
# 5: Riga      (4 days) – Attend a conference in Riga between day 15 and day 18, force arrival = 15.
# 6: Paris     (5 days)
#
# Total raw days = 3 + 4 + 3 + 5 + 3 + 4 + 5 = 27.
# There are 6 transitions between 7 visits, so overall trip length = 27 - 6 = 21 days.
cities = ["Munich", "Hamburg", "Lyon", "Stockholm", "Berlin", "Riga", "Paris"]
durations = [3, 4, 3, 5, 3, 4, 5]

# Allowed direct flights:
# 1. Berlin and Munich         -> bidirectional: (4,0)
# 2. Munich and Hamburg        -> bidirectional: (0,1)
# 3. Lyon and Munich           -> bidirectional: (2,0)
# 4. Berlin and Stockholm      -> bidirectional: (4,3)
# 5. Paris and Riga            -> bidirectional: (6,5)
# 6. Paris and Munich          -> bidirectional: (6,0)
# 7. Stockholm and Riga        -> bidirectional: (3,5)
# 8. Munich and Stockholm      -> bidirectional: (0,3)
# 9. Paris and Berlin          -> bidirectional: (6,4)
# 10. from Riga to Hamburg     -> one-way: (5,1) only
# 11. Paris and Hamburg        -> bidirectional: (6,1)
# 12. Paris and Stockholm      -> bidirectional: (6,3)
# 13. Lyon and Paris           -> bidirectional: (2,6)
# 14. Stockholm and Hamburg    -> bidirectional: (3,1)
# 15. from Riga to Munich      -> one-way: (5,0) only
# 16. Berlin and Riga          -> bidirectional: (4,5)

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Berlin <-> Munich
bidir(4, 0)
# 2. Munich <-> Hamburg
bidir(0, 1)
# 3. Lyon <-> Munich
bidir(2, 0)
# 4. Berlin <-> Stockholm
bidir(4, 3)
# 5. Paris <-> Riga
bidir(6, 5)
# 6. Paris <-> Munich
bidir(6, 0)
# 7. Stockholm <-> Riga
bidir(3, 5)
# 8. Munich <-> Stockholm
bidir(0, 3)
# 9. Paris <-> Berlin
bidir(6, 4)
# 10. from Riga to Hamburg (one-way)
allowed_flights.append((5, 1))
# 11. Paris <-> Hamburg
bidir(6, 1)
# 12. Paris <-> Stockholm
bidir(6, 3)
# 13. Lyon <-> Paris
bidir(2, 6)
# 14. Stockholm <-> Hamburg
bidir(3, 1)
# 15. from Riga to Munich (one-way)
allowed_flights.append((5, 0))
# 16. Berlin <-> Riga
bidir(4, 5)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the visitation order as a permutation of city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit in the itinerary.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# Each visit: departure = arrival + (duration - 1)
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share a transit day:
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip finishes on day 21.
s.add(departures[n-1] == 21)

# Event-specific constraints:
# Munich (city 0): meet a friend between day 9 and 11 → force arrival = 9.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 9, True))
# Berlin (city 4): attend a workshop between day 7 and 9 → force arrival = 7.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 7, True))
# Riga (city 5): attend a conference between day 15 and 18 → force arrival = 15.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 15, True))

# Connectivity constraints:
# For every consecutive pair, there must be a direct flight between them.
for i in range(n - 1):
    flight_opts = []
    for (frm, to) in allowed_flights:
        flight_opts.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*flight_opts))

# Solve the model and print the itinerary.
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