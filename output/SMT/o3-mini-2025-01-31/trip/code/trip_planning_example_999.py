from z3 import *

# City indices and durations:
# 0: Nice      (2 days)
# 1: Warsaw    (2 days)
# 2: Bucharest (5 days)
# 3: Lyon      (2 days) – Annual show in Lyon from day 16 to day 17 → force arrival = 16.
# 4: Naples    (4 days) – Conference in Naples during day 1 and day 4 → force arrival = 1.
# 5: Edinburgh (4 days)
# 6: Hamburg   (4 days) – Meet friends in Hamburg between day 9 and 12 → force arrival = 9.
#
# Total raw days = 2 + 2 + 5 + 2 + 4 + 4 + 4 = 23.
# With 6 overlaps (between the 7 visits) the overall trip length = 23 - 6 = 17 days.

cities = ["Nice", "Warsaw", "Bucharest", "Lyon", "Naples", "Edinburgh", "Hamburg"]
durations = [2, 2, 5, 2, 4, 4, 4]

# Allowed direct flights (all bidirectional):
# 1. Naples and Nice
# 2. Edinburgh and Hamburg
# 3. Warsaw and Bucharest
# 4. Nice and Lyon
# 5. Naples and Bucharest
# 6. Nice and Edinburgh
# 7. Nice and Hamburg
# 8. Bucharest and Lyon
# 9. Naples and Warsaw
# 10. Hamburg and Bucharest
# 11. Warsaw and Hamburg
# 12. Warsaw and Nice

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Naples <-> Nice
add_bidirectional(4, 0)
# 2. Edinburgh <-> Hamburg
add_bidirectional(5, 6)
# 3. Warsaw <-> Bucharest
add_bidirectional(1, 2)
# 4. Nice <-> Lyon
add_bidirectional(0, 3)
# 5. Naples <-> Bucharest
add_bidirectional(4, 2)
# 6. Nice <-> Edinburgh
add_bidirectional(0, 5)
# 7. Nice <-> Hamburg
add_bidirectional(0, 6)
# 8. Bucharest <-> Lyon
add_bidirectional(2, 3)
# 9. Naples <-> Warsaw
add_bidirectional(4, 1)
# 10. Hamburg <-> Bucharest
add_bidirectional(6, 2)
# 11. Warsaw <-> Hamburg
add_bidirectional(1, 6)
# 12. Warsaw <-> Nice
add_bidirectional(1, 0)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Represent the itinerary as a permutation of the city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Define arrival and departure day variables for each visit in the itinerary.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot, if city c is assigned then its departure is arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: arrival of visit i+1 equals departure of visit i.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 17.
s.add(departures[n-1] == 17)

# Event-specific constraints:
# Lyon (index 3): Annual show from day 16 to 17 → force arrival = 16.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 16, True))
# Naples (index 4): Conference during day 1 to 4 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 1, True))
# Hamburg (index 6): Meet friends between day 9 and 12 → force arrival = 9.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 9, True))

# Connectivity constraints:
# Each consecutive pair of cities in the itinerary must be connected by a direct flight.
for i in range(n-1):
    s.add(Or([And(order[i] == frm, order[i+1] == to)
              for (frm, to) in allowed_flights]))

# Solve the model and print the itinerary.
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