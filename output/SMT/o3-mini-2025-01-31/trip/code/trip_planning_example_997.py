from z3 import *

# City indices and durations:
# 0: Reykjavik  (5 days) – Annual show from day 11 to 15 → force arrival = 11.
# 1: Munich     (3 days) – Wedding from day 5 to 7 → force arrival = 5.
# 2: Venice     (5 days)
# 3: Salzburg   (4 days) – Workshop from day 22 to 25 → force arrival = 22.
# 4: Prague     (5 days)
# 5: Hamburg    (4 days)
# 6: Warsaw     (5 days)
#
# Total raw days = 5 + 3 + 5 + 4 + 5 + 4 + 5 = 31.
# With 6 overlaps between visits, overall trip length = 31 - 6 = 25 days.

cities = ["Reykjavik", "Munich", "Venice", "Salzburg", "Prague", "Hamburg", "Warsaw"]
durations = [5, 3, 5, 4, 5, 4, 5]

# Allowed direct flights (bidirectional):
# 1. Munich and Warsaw         -> (1,6) and (6,1)
# 2. Prague and Warsaw         -> (4,6) and (6,4)
# 3. Warsaw and Hamburg        -> (6,5) and (5,6)
# 4. Venice and Munich         -> (2,1) and (1,2)
# 5. Prague and Reykjavik      -> (4,0) and (0,4)
# 6. Venice and Warsaw         -> (2,6) and (6,2)
# 7. Venice and Hamburg        -> (2,5) and (5,2)
# 8. Munich and Reykjavik      -> (1,0) and (0,1)
# 9. Hamburg and Salzburg      -> (5,3) and (3,5)
# 10. Reykjavik and Warsaw     -> (0,6) and (6,0)
# 11. Munich and Prague        -> (1,4) and (4,1)
# 12. Munich and Hamburg       -> (1,5) and (5,1)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Munich <-> Warsaw
add_bidirectional(1, 6)
# 2. Prague <-> Warsaw
add_bidirectional(4, 6)
# 3. Warsaw <-> Hamburg
add_bidirectional(6, 5)
# 4. Venice <-> Munich
add_bidirectional(2, 1)
# 5. Prague <-> Reykjavik
add_bidirectional(4, 0)
# 6. Venice <-> Warsaw
add_bidirectional(2, 6)
# 7. Venice <-> Hamburg
add_bidirectional(2, 5)
# 8. Munich <-> Reykjavik
add_bidirectional(1, 0)
# 9. Hamburg <-> Salzburg
add_bidirectional(5, 3)
# 10. Reykjavik <-> Warsaw
add_bidirectional(0, 6)
# 11. Munich <-> Prague
add_bidirectional(1, 4)
# 12. Munich <-> Hamburg
add_bidirectional(1, 5)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 visits

# Represent the itinerary as a permutation of the cities.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit, if city c is visited then departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: arrival of visit i+1 equals departure of visit i.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 25.
s.add(departures[n-1] == 25)

# Event-specific constraints:
# Reykjavik (index 0): Annual show → force arrival = 11.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 11, True))
# Munich (index 1): Wedding → force arrival = 5.
for i in range(n):
    s.add(If(order[i] == 1, arrivals[i] == 5, True))
# Salzburg (index 3): Workshop → force arrival = 22.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 22, True))

# Connectivity constraints:
# Each consecutive pair must be connected by a direct flight.
for i in range(n - 1):
    connection_options = []
    for (frm, to) in allowed_flights:
        connection_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(connection_options))

# Solve and print the itinerary.
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