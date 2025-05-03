from z3 import *

# Cities:
# 0: Naples      (5 days)
# 1: Bucharest   (3 days)
# 2: Riga        (3 days)
# 3: Split       (2 days)
# 4: Reykjavik   (4 days)
# 5: Stuttgart   (2 days) – Meet friends between day 4 and day 5 ⇒ force arrival = 4.
# 6: Istanbul    (5 days) – Workshop between day 5 and day 9 ⇒ force arrival = 5.
#
# Total raw days = 5 + 3 + 3 + 2 + 4 + 2 + 5 = 24.
# There are 6 transitions (each pair shares one day), so overall trip length = 24 - 6 = 18 days.
cities = ["Naples", "Bucharest", "Riga", "Split", "Reykjavik", "Stuttgart", "Istanbul"]
durations = [5, 3, 3, 2, 4, 2, 5]

# Allowed direct flights:
# (Bucharest, Naples) and reverse: (1,0) and (0,1)
# (Stuttgart, Naples) and reverse: (5,0) and (0,5)
# (Naples, Split) and reverse: (0,3) and (3,0)
# from Reykjavik to Stuttgart: only (4,5)
# (Stuttgart, Split) and reverse: (5,3) and (3,5)
# (Istanbul, Riga) and reverse: (6,2) and (2,6)
# (Istanbul, Bucharest) and reverse: (6,1) and (1,6)
# (Stuttgart, Istanbul) and reverse: (5,6) and (6,5)
# (Istanbul, Naples) and reverse: (6,0) and (0,6)
# (Riga, Bucharest) and reverse: (2,1) and (1,2)
allowed_flights = [
    (1, 0), (0, 1), 
    (5, 0), (0, 5),
    (0, 3), (3, 0),
    (4, 5),  # Only from Reykjavik to Stuttgart!
    (5, 3), (3, 5),
    (6, 2), (2, 6),
    (6, 1), (1, 6),
    (5, 6), (6, 5),
    (6, 0), (0, 6),
    (2, 1), (1, 2)
]

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the visitation order as a permutation of the city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, the departure day is computed as:
# departure = arrival + (duration - 1)
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share a transit day:
# arrival of visit i+1 equals departure of visit i.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 18.
s.add(departures[n-1] == 18)

# Time-specific event constraints:
# Stuttgart (city 5): meet friends between day 4 and 5 so force arrival = 4.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 4, True))
# Istanbul (city 6): workshop between day 5 and 9 so force arrival = 5.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 5, True))

# Connectivity constraints:
# For each consecutive pair of visits, the directed flight from the city in the earlier slot 
# to the city in the next slot must be allowed.
for i in range(n - 1):
    flight_options = []
    for (frm, to) in allowed_flights:
        flight_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*flight_options))

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