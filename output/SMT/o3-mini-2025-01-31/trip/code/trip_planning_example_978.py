from z3 import *

# City indices and durations:
# 0: Reykjavik (5 days)
# 1: Munich    (2 days) – Meet friends in Munich between day 1 and day 2 → force arrival = 1.
# 2: Barcelona (4 days)
# 3: Istanbul  (2 days) – Annual show in Istanbul between day 2 and day 3 → force arrival = 2.
# 4: Lisbon    (4 days) – Visit relatives in Lisbon between day 10 and day 13 → force arrival = 10.
# 5: Dubrovnik (5 days)
# 6: Madrid    (2 days)
#
# Total raw days = 5 + 2 + 4 + 2 + 4 + 5 + 2 = 24.
# With 6 overlapping transit days for 7 visits, overall trip length = 24 - 6 = 18 days.

cities = ["Reykjavik", "Munich", "Barcelona", "Istanbul", "Lisbon", "Dubrovnik", "Madrid"]
durations = [5, 2, 4, 2, 4, 5, 2]

# Allowed direct flights:
# 1. Reykjavik and Lisbon                  -> bidirectional: (0,4)
# 2. Munich and Barcelona                  -> bidirectional: (1,2)
# 3. Munich and Dubrovnik                  -> bidirectional: (1,5)
# 4. Munich and Reykjavik                  -> bidirectional: (1,0)
# 5. Barcelona and Dubrovnik               -> bidirectional: (2,5)
# 6. from Reykjavik to Madrid              -> one-way: (0,6)
# 7. Munich and Istanbul                   -> bidirectional: (1,3)
# 8. from Dubrovnik to Istanbul            -> one-way: (5,3)
# 9. Barcelona and Reykjavik               -> bidirectional: (2,0)
# 10. Barcelona and Madrid                 -> bidirectional: (2,6)
# 11. Istanbul and Madrid                  -> bidirectional: (3,6)
# 12. Munich and Madrid                    -> bidirectional: (1,6)
# 13. Munich and Lisbon                    -> bidirectional: (1,4)
# 14. Barcelona and Lisbon                 -> bidirectional: (2,4)
# 15. Lisbon and Madrid                    -> bidirectional: (4,6)
# 16. Istanbul and Barcelona               -> bidirectional: (3,2)
# 17. Madrid and Dubrovnik                 -> bidirectional: (6,5)
# 18. Istanbul and Lisbon                  -> bidirectional: (3,4)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Reykjavik <-> Lisbon
add_bidirectional(0, 4)
# 2. Munich <-> Barcelona
add_bidirectional(1, 2)
# 3. Munich <-> Dubrovnik
add_bidirectional(1, 5)
# 4. Munich <-> Reykjavik
add_bidirectional(1, 0)
# 5. Barcelona <-> Dubrovnik
add_bidirectional(2, 5)
# 6. One-way: Reykjavik -> Madrid
allowed_flights.append((0, 6))
# 7. Munich <-> Istanbul
add_bidirectional(1, 3)
# 8. One-way: Dubrovnik -> Istanbul
allowed_flights.append((5, 3))
# 9. Barcelona <-> Reykjavik
add_bidirectional(2, 0)
# 10. Barcelona <-> Madrid
add_bidirectional(2, 6)
# 11. Istanbul <-> Madrid
add_bidirectional(3, 6)
# 12. Munich <-> Madrid
add_bidirectional(1, 6)
# 13. Munich <-> Lisbon
add_bidirectional(1, 4)
# 14. Barcelona <-> Lisbon
add_bidirectional(2, 4)
# 15. Lisbon <-> Madrid
add_bidirectional(4, 6)
# 16. Istanbul <-> Barcelona
add_bidirectional(3, 2)
# 17. Madrid <-> Dubrovnik
add_bidirectional(6, 5)
# 18. Istanbul <-> Lisbon
add_bidirectional(3, 4)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Permutation: order[i] is the city index visited in the i-th slot.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if city c is visited then:
# departure[i] = arrival[i] + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: next arrival equals previous departure.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 18.
s.add(departures[n-1] == 18)

# Event-specific constraints:
# Munich (city index 1): meet friends between day 1 and day 2 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 1, arrivals[i] == 1, True))
# Istanbul (city index 3): annual show between day 2 and day 3 → force arrival = 2.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 2, True))
# Lisbon (city index 4): visit relatives between day 10 and day 13 → force arrival = 10.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 10, True))

# Connectivity constraints:
# Each consecutive pair of cities must be connected by a direct flight.
for i in range(n-1):
    connection_options = []
    for (frm, to) in allowed_flights:
        connection_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*connection_options))

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