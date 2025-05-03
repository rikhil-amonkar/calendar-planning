from z3 import *

# City indices and durations:
# 0: Mykonos   (4 days)
# 1: Florence  (4 days) – Workshop in Florence between day 10 and 13 → force arrival = 10.
# 2: Zurich    (2 days)
# 3: Barcelona (4 days)
# 4: Amsterdam (4 days)
# 5: Seville   (3 days)
# 6: Bucharest (3 days) – Meet friends in Bucharest between day 16 and 18 → force arrival = 16.
#
# Total raw days = 4 + 4 + 2 + 4 + 4 + 3 + 3 = 24.
# With 6 overlapping transit days among 7 visits, overall trip length = 24 - 6 = 18 days.

cities = ["Mykonos", "Florence", "Zurich", "Barcelona", "Amsterdam", "Seville", "Bucharest"]
durations = [4, 4, 2, 4, 4, 3, 3]

# Allowed direct flights:
# 1. Amsterdam and Bucharest   -> (Amsterdam, Bucharest)           => (4,6)
# 2. Florence and Barcelona    -> (Florence, Barcelona)            => (1,3)
# 3. Amsterdam and Barcelona   -> (Amsterdam, Barcelona)           => (4,3)
# 4. Amsterdam and Mykonos     -> (Amsterdam, Mykonos)             => (4,0)
# 5. Mykonos and Zurich        -> (Mykonos, Zurich)                => (0,2)
# 6. Seville and Barcelona     -> (Seville, Barcelona)             => (5,3)
# 7. Seville and Amsterdam     -> (Seville, Amsterdam)             => (5,4)
# 8. from Zurich to Florence   -> one-way: (Zurich, Florence)      => (2,1)
# 9. Zurich and Bucharest      -> (Zurich, Bucharest)              => (2,6)
# 10. Barcelona and Bucharest  -> (Barcelona, Bucharest)           => (3,6)
# 11. Amsterdam and Zurich     -> (Amsterdam, Zurich)              => (4,2)
# 12. Amsterdam and Florence   -> (Amsterdam, Florence)            => (4,1)
# 13. Zurich and Barcelona     -> (Zurich, Barcelona)              => (2,3)

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Amsterdam <-> Bucharest
bidir(4, 6)

# 2. Florence <-> Barcelona
bidir(1, 3)

# 3. Amsterdam <-> Barcelona
bidir(4, 3)

# 4. Amsterdam <-> Mykonos
bidir(4, 0)

# 5. Mykonos <-> Zurich
bidir(0, 2)

# 6. Seville <-> Barcelona
bidir(5, 3)

# 7. Seville <-> Amsterdam
bidir(5, 4)

# 8. One-way: from Zurich to Florence only (not Florence to Zurich)
allowed_flights.append((2, 1))

# 9. Zurich <-> Bucharest
bidir(2, 6)

# 10. Barcelona <-> Bucharest
bidir(3, 6)

# 11. Amsterdam <-> Zurich
bidir(4, 2)

# 12. Amsterdam <-> Florence
bidir(4, 1)

# 13. Zurich <-> Barcelona
bidir(2, 3)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # number of cities = 7

# The itinerary is modeled as a permutation of the cities.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Arrival and departure day for each visit.
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
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 18.
s.add(departures[n-1] == 18)

# Event-specific constraints:
# Florence (city index 1): Workshop between day 10 and 13 → force arrival = 10.
for i in range(n):
    s.add(If(order[i] == 1, arrivals[i] == 10, True))
# Bucharest (city index 6): Meet friends between day 16 and 18 → force arrival = 16.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 16, True))

# Connectivity constraints: Each consecutive pair of cities must be connected by a direct flight.
for i in range(n - 1):
    flight_options = []
    for (frm, to) in allowed_flights:
        flight_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*flight_options))

# Solve the model and output the itinerary.
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