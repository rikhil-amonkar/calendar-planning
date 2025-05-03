from z3 import *

# Cities and durations with event constraints:
# 0: Madrid   (4 days)
# 1: Geneva   (2 days)
# 2: Mykonos  (5 days)
# 3: Milan    (3 days)  – Relatives in Milan between day 5 and day 7 → force arrival = 5.
# 4: Zurich   (5 days)
# 5: Florence (4 days)  – Conference in Florence between day 15 and day 18 → force arrival = 15.
# 6: Dublin   (5 days)  – Meet friends in Dublin between day 1 and day 5 → force arrival = 1.
#
# Total raw days = 4 + 2 + 5 + 3 + 5 + 4 + 5 = 28.
# There are 6 overlaps between visits, so overall trip length = 28 - 6 = 22 days.

cities = ["Madrid", "Geneva", "Mykonos", "Milan", "Zurich", "Florence", "Dublin"]
durations = [4, 2, 5, 3, 5, 4, 5]

# Allowed direct flights:
# 1. Mykonos and Madrid           -> (Mykonos, Madrid)         => (2, 0)
# 2. Zurich and Madrid            -> (Zurich, Madrid)          => (4, 0)
# 3. Dublin and Geneva            -> (Dublin, Geneva)          => (6, 1)
# 4. Mykonos and Geneva           -> (Mykonos, Geneva)         => (2, 1)
# 5. Mykonos and Zurich           -> (Mykonos, Zurich)         => (2, 4)
# 6. Milan and Zurich             -> (Milan, Zurich)           => (3, 4)
# 7. Milan and Mykonos            -> (Milan, Mykonos)          => (3, 2)
# 8. Dublin and Madrid            -> (Dublin, Madrid)          => (6, 0)
# 9. Florence and Madrid          -> (Florence, Madrid)        => (5, 0)
# 10. Zurich and Geneva           -> (Zurich, Geneva)          => (4, 1)
# 11. from Zurich to Florence     -> one-way: (Zurich, Florence) => (4, 5)
# 12. Milan and Madrid            -> (Milan, Madrid)           => (3, 0)
# 13. Madrid and Geneva           -> (Madrid, Geneva)          => (0, 1)
# 14. Dublin and Milan            -> (Dublin, Milan)           => (6, 3)
# 15. Dublin and Zurich           -> (Dublin, Zurich)          => (6, 4)

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Mykonos <-> Madrid
bidir(2, 0)
# 2. Zurich <-> Madrid
bidir(4, 0)
# 3. Dublin <-> Geneva
bidir(6, 1)
# 4. Mykonos <-> Geneva
bidir(2, 1)
# 5. Mykonos <-> Zurich
bidir(2, 4)
# 6. Milan <-> Zurich
bidir(3, 4)
# 7. Milan <-> Mykonos
bidir(3, 2)
# 8. Dublin <-> Madrid
bidir(6, 0)
# 9. Florence <-> Madrid
bidir(5, 0)
# 10. Zurich <-> Geneva
bidir(4, 1)
# 11. One-way: from Zurich to Florence
allowed_flights.append((4, 5))
# 12. Milan <-> Madrid
bidir(3, 0)
# 13. Madrid <-> Geneva
bidir(0, 1)
# 14. Dublin <-> Milan
bidir(6, 3)
# 15. Dublin <-> Zurich
bidir(6, 4)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the order in which cities are visited as a permutation:
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit, departure day is defined by: departure = arrival + (duration - 1).
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share one transit day:
for i in range(n - 1):
    s.add(arrivals[i + 1] == departures[i])

# The overall trip must finish on day 22.
s.add(departures[n - 1] == 22)

# Event-specific constraints:
# Dublin (city 6): meet friends between day 1 and 5 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 1, True))
# Milan (city 3): visit relatives between day 5 and 7 → force arrival = 5.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 5, True))
# Florence (city 5): conference between day 15 and 18 → force arrival = 15.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 15, True))

# Connectivity constraints:
# Each consecutive pair of visits must be connected by a direct flight.
for i in range(n - 1):
    flights_possible = []
    for (frm, to) in allowed_flights:
        flights_possible.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*flights_possible))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_idx]:10s}: [{a_day}, {d_day}]")
else:
    print("No solution found")