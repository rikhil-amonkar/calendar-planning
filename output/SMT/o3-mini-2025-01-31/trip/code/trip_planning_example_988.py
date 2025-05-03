from z3 import *

# City indices and durations:
# 0: Athens    (3 days)
# 1: Zurich    (3 days)
# 2: Reykjavik (2 days)
# 3: Tallinn   (4 days) – Meet friends in Tallinn between day 14 and 17 → force arrival = 14.
# 4: Mykonos   (3 days) – Annual show in Mykonos from day 3 to 5 → force arrival = 3.
# 5: Lisbon    (5 days) – Wedding in Lisbon between day 8 and 12 → force arrival = 8.
# 6: Vienna    (3 days)
#
# Total raw days = 3 + 3 + 2 + 4 + 3 + 5 + 3 = 23.
# There are 6 overlaps (for 7 cities), so overall trip length = 23 - 6 = 17 days.

cities = ["Athens", "Zurich", "Reykjavik", "Tallinn", "Mykonos", "Lisbon", "Vienna"]
durations = [3, 3, 2, 4, 3, 5, 3]

# Allowed direct flights:
# (city indices as defined above)
# 1. Athens and Mykonos: (0,4)
# 2. Athens and Vienna:    (0,6)
# 3. Vienna and Lisbon:    (6,5)
# 4. Athens and Zurich:    (0,1)
# 5. Reykjavik and Zurich: (2,1)
# 6. Athens and Lisbon:    (0,5)
# 7. Zurich and Tallinn:   (1,3)
# 8. Mykonos and Zurich:   (4,1)
# 9. Vienna and Reykjavik: (6,2)
# 10. Lisbon and Zurich:   (5,1)
# 11. Reykjavik and Lisbon:(2,5)
# 12. from Reykjavik to Athens (one-way): (2,0)
# 13. Mykonos and Vienna:  (4,6)
# 14. Vienna and Zurich:   (6,1)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Athens <-> Mykonos
add_bidirectional(0, 4)
# 2. Athens <-> Vienna
add_bidirectional(0, 6)
# 3. Vienna <-> Lisbon
add_bidirectional(6, 5)
# 4. Athens <-> Zurich
add_bidirectional(0, 1)
# 5. Reykjavik <-> Zurich
add_bidirectional(2, 1)
# 6. Athens <-> Lisbon
add_bidirectional(0, 5)
# 7. Zurich <-> Tallinn
add_bidirectional(1, 3)
# 8. Mykonos <-> Zurich
add_bidirectional(4, 1)
# 9. Vienna <-> Reykjavik
add_bidirectional(6, 2)
# 10. Lisbon <-> Zurich
add_bidirectional(5, 1)
# 11. Reykjavik <-> Lisbon
add_bidirectional(2, 5)
# 12. One-way from Reykjavik to Athens
allowed_flights.append((2, 0))
# 13. Mykonos <-> Vienna
add_bidirectional(4, 6)
# 14. Vienna <-> Zurich
add_bidirectional(6, 1)

# Set up Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the permutation order of city visits.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if city c is visited then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: arrival of next equals departure of previous.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 17.
s.add(departures[n-1] == 17)

# Event-specific constraints:
# Tallinn (index 3): Meet friends between day 14 and 17 → force arrival = 14.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 14, True))
# Mykonos (index 4): Annual show between day 3 and 5 → force arrival = 3.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 3, True))
# Lisbon (index 5): Wedding between day 8 and 12 → force arrival = 8.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 8, True))

# Connectivity constraints:
# Each consecutive pair of visited cities must be connected by an allowed direct flight.
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