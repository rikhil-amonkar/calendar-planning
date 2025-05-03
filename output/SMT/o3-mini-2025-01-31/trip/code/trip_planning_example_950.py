from z3 import *

# We have 7 cities with the following assigned indices and durations:
# 0: Mykonos   (3 days) – Wedding between day 4 and day 6, so force arrival = 4.
# 1: Riga      (3 days)
# 2: Munich    (4 days)
# 3: Bucharest (4 days)
# 4: Rome      (4 days) – Conference between day 1 and day 4, so force arrival = 1.
# 5: Nice      (3 days)
# 6: Krakow    (2 days) – Annual show between day 16 and 17, so force arrival = 16.
#
# Total raw days = 3 + 3 + 4 + 4 + 4 + 3 + 2 = 23.
# We have 6 transitions (each pair shares one day),
# so the overall trip length = 23 - 6 = 17 days.
cities = ["Mykonos", "Riga", "Munich", "Bucharest", "Rome", "Nice", "Krakow"]
durations = [3, 3, 4, 4, 4, 3, 2]

# Allowed direct flights:
# The flights are given as follows (city index in parentheses):
# 1. Nice and Riga               → bidir(5, 1)
# 2. Bucharest and Munich          → bidir(3, 2)
# 3. Mykonos and Munich            → bidir(0, 2)
# 4. Riga and Bucharest            → bidir(1, 3)
# 5. Rome and Nice                → bidir(4, 5)
# 6. Rome and Munich               → bidir(4, 2)
# 7. Mykonos and Nice              → bidir(0, 5)
# 8. Rome and Mykonos              → bidir(4, 0)
# 9. Munich and Krakow             → bidir(2, 6)
# 10. Rome and Bucharest           → bidir(4, 3)
# 11. Nice and Munich              → bidir(5, 2)
# 12. from Riga to Munich          → one-way: (1, 2) only
# 13. from Rome to Riga            → one-way: (4, 1) only

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Nice (5) and Riga (1)
bidir(5, 1)
# 2. Bucharest (3) and Munich (2)
bidir(3, 2)
# 3. Mykonos (0) and Munich (2)
bidir(0, 2)
# 4. Riga (1) and Bucharest (3)
bidir(1, 3)
# 5. Rome (4) and Nice (5)
bidir(4, 5)
# 6. Rome (4) and Munich (2)
bidir(4, 2)
# 7. Mykonos (0) and Nice (5)
bidir(0, 5)
# 8. Rome (4) and Mykonos (0)
bidir(4, 0)
# 9. Munich (2) and Krakow (6)
bidir(2, 6)
# 10. Rome (4) and Bucharest (3)
bidir(4, 3)
# 11. Nice (5) and Munich (2)
bidir(5, 2)
# 12. from Riga to Munich: one-way (from 1 to 2)
allowed_flights.append((1, 2))
# 13. from Rome to Riga: one-way (from 4 to 1)
allowed_flights.append((4, 1))

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define visitation order as a permutation of city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit in the order.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot, departure = arrival + duration - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share one transit day: arrival of next equals departure of previous.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 17.
s.add(departures[n-1] == 17)

# Time-specific event constraints:
# Rome (city 4): conference between day1 and day4, force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 1, True))
# Mykonos (city 0): wedding between day4 and day6, force arrival = 4.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 4, True))
# Krakow (city 6): annual show between day16 and day17, force arrival = 16.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 16, True))

# Connectivity constraints:
# For every consecutive pair in the itinerary, there must be an allowed direct flight from
# the earlier city to the later city (respecting one-way directions).
for i in range(n - 1):
    flight_options = []
    for (frm, to) in allowed_flights:
        flight_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*flight_options))

# Solve and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_idx]:9s}: [{a_day}, {d_day}]")
else:
    print("No solution found")