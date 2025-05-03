from z3 import *

# Cities with indices, durations, and event constraints:
# 0: Zurich    (5 days) – Visit relatives in Zurich between day 11 and day 15 ⇒ force arrival = 11.
# 1: Vilnius   (2 days)
# 2: Frankfurt (3 days)
# 3: Porto     (3 days) – Wedding in Porto between day 3 and day 5 ⇒ force arrival = 3.
# 4: Mykonos   (2 days)
# 5: London    (5 days) – Meet friends in London between day 7 and day 11 ⇒ force arrival = 7.
# 6: Amsterdam (2 days)
#
# Total raw days = 5 + 2 + 3 + 3 + 2 + 5 + 2 = 22.
# There are 6 transitions (each consecutive visit shares one day),
# so overall trip length = 22 - 6 = 16 days.
cities = ["Zurich", "Vilnius", "Frankfurt", "Porto", "Mykonos", "London", "Amsterdam"]
durations = [5, 2, 3, 3, 2, 5, 2]

# Allowed direct flights (bidirectional unless otherwise noted):
# 1. Amsterdam and London     -> (Amsterdam, London) : (6, 5)
# 2. Mykonos and London        -> (Mykonos, London)    : (4, 5)
# 3. Frankfurt and London      -> (Frankfurt, London)  : (2, 5)
# 4. Frankfurt and Amsterdam   -> (Frankfurt, Amsterdam): (2, 6)
# 5. Porto and Zurich          -> (Porto, Zurich)      : (3, 0)
# 6. Frankfurt and Zurich      -> (Frankfurt, Zurich)  : (2, 0)
# 7. Zurich and Vilnius        -> (Zurich, Vilnius)    : (0, 1)
# 8. Frankfurt and Porto       -> (Frankfurt, Porto)   : (2, 3)
# 9. Porto and Amsterdam       -> (Porto, Amsterdam)   : (3, 6)
# 10. Mykonos and Zurich       -> (Mykonos, Zurich)    : (4, 0)
# 11. Amsterdam and Mykonos    -> (Amsterdam, Mykonos) : (6, 4)
# 12. Amsterdam and Vilnius    -> (Amsterdam, Vilnius) : (6, 1)
# 13. London and Zurich        -> (London, Zurich)     : (5, 0)
# 14. Amsterdam and Zurich     -> (Amsterdam, Zurich)  : (6, 0)
# 15. Frankfurt and Vilnius    -> (Frankfurt, Vilnius) : (2, 1)

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Amsterdam <-> London
bidir(6, 5)
# 2. Mykonos <-> London
bidir(4, 5)
# 3. Frankfurt <-> London
bidir(2, 5)
# 4. Frankfurt <-> Amsterdam
bidir(2, 6)
# 5. Porto <-> Zurich
bidir(3, 0)
# 6. Frankfurt <-> Zurich
bidir(2, 0)
# 7. Zurich <-> Vilnius
bidir(0, 1)
# 8. Frankfurt <-> Porto
bidir(2, 3)
# 9. Porto <-> Amsterdam
bidir(3, 6)
# 10. Mykonos <-> Zurich
bidir(4, 0)
# 11. Amsterdam <-> Mykonos
bidir(6, 4)
# 12. Amsterdam <-> Vilnius
bidir(6, 1)
# 13. London <-> Zurich
bidir(5, 0)
# 14. Amsterdam <-> Zurich
bidir(6, 0)
# 15. Frankfurt <-> Vilnius
bidir(2, 1)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the visitation order as a permutation of the city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, set departure = arrival + duration - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share a transit day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 16.
s.add(departures[n-1] == 16)

# Event-specific time constraints:
# Zurich (city 0): visit relatives between day 11 and day 15 => force arrival = 11.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 11, True))
# Porto (city 3): wedding between day 3 and day 5 => force arrival = 3.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 3, True))
# London (city 5): meet friends between day 7 and day 11 => force arrival = 7.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 7, True))

# Connectivity constraints:
# Each consecutive pair of cities must be connected by a direct flight.
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
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:10s}: [{a_day}, {d_day}]")
else:
    print("No solution found")