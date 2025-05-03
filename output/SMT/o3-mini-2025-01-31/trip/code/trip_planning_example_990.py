from z3 import *

# City indices and durations:
# 0: Istanbul   (3 days)
# 1: Reykjavik  (2 days)
# 2: Berlin     (5 days) – Visit relatives in Berlin between day 5 and day 9 → force arrival = 5.
# 3: Rome       (3 days) – Meet friends in Rome between day 2 and day 4 → force arrival = 2.
# 4: Tallinn    (5 days)
# 5: Hamburg    (2 days)
# 6: Warsaw     (4 days) – Workshop in Warsaw between day 15 and day 18 → force arrival = 15.
#
# Total raw days = 3 + 2 + 5 + 3 + 5 + 2 + 4 = 24.
# With 6 overlaps (7 cities visited consecutively), overall trip length = 24 - 6 = 18 days.

cities = ["Istanbul", "Reykjavik", "Berlin", "Rome", "Tallinn", "Hamburg", "Warsaw"]
durations = [3, 2, 5, 3, 5, 2, 4]

# Allowed direct flights:
# 1. Hamburg and Istanbul
# 2. Rome and Warsaw
# 3. Istanbul and Warsaw
# 4. Berlin and Warsaw
# 5. Reykjavik and Warsaw
# 6. Rome and Istanbul
# 7. Hamburg and Rome
# 8. Rome and Berlin
# 9. Tallinn and Warsaw
# 10. Reykjavik and Berlin
# 11. from Istanbul to Tallinn (one-way)
# 12. Berlin and Tallinn
# 13. Rome and Reykjavik
# 14. Hamburg and Warsaw
# 15. Berlin and Istanbul

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))
    
# 1. Hamburg <-> Istanbul
add_bidirectional(5, 0)
# 2. Rome <-> Warsaw
add_bidirectional(3, 6)
# 3. Istanbul <-> Warsaw
add_bidirectional(0, 6)
# 4. Berlin <-> Warsaw
add_bidirectional(2, 6)
# 5. Reykjavik <-> Warsaw
add_bidirectional(1, 6)
# 6. Rome <-> Istanbul
add_bidirectional(3, 0)
# 7. Hamburg <-> Rome
add_bidirectional(5, 3)
# 8. Rome <-> Berlin
add_bidirectional(3, 2)
# 9. Tallinn <-> Warsaw
add_bidirectional(4, 6)
# 10. Reykjavik <-> Berlin
add_bidirectional(1, 2)
# 11. One-way from Istanbul to Tallinn
allowed_flights.append((0, 4))
# 12. Berlin <-> Tallinn
add_bidirectional(2, 4)
# 13. Rome <-> Reykjavik
add_bidirectional(3, 1)
# 14. Hamburg <-> Warsaw
add_bidirectional(5, 6)
# 15. Berlin <-> Istanbul
add_bidirectional(2, 0)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# The itinerary (order) is modeled as a permutation of 0..6.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Define arrival and departure day variables for each visit in the itinerary.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the city c is visited then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: The arrival time of the next city equals the departure of the previous one.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 18.
s.add(departures[n-1] == 18)

# Event-specific constraints:
# Berlin (index 2): Visit relatives between day 5 and day 9 → force arrival at 5.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 5, True))
# Rome (index 3): Meet friends between day 2 and day 4 → force arrival at 2.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 2, True))
# Warsaw (index 6): Workshop between day 15 and day 18 → force arrival at 15.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 15, True))

# Connectivity constraints:
# Each consecutive pair of cities must be connected by one of the allowed direct flights.
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