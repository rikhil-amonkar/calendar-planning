from z3 import *

# Define the 7 cities along with durations and event constraints:
# 0: Stockholm  (4 days) – meet friend between day 6 and day 9 ⇒ force arrival = 6.
# 1: Tallinn    (3 days) – meet friends between day 4 and day 6   ⇒ force arrival = 4.
# 2: Rome       (4 days) – wedding between day 10 and day 13       ⇒ force arrival = 10.
# 3: Budapest   (2 days)
# 4: Prague     (3 days)
# 5: Krakow     (2 days)
# 6: Vienna     (2 days)
#
# Total raw days = 4 + 3 + 4 + 2 + 3 + 2 + 2 = 20.
# There are 6 transitions (each consecutive visit shares one day),
# so overall trip length = 20 - 6 = 14 days.
cities = ["Stockholm", "Tallinn", "Rome", "Budapest", "Prague", "Krakow", "Vienna"]
durations = [4, 3, 4, 2, 3, 2, 2]

# Allowed direct flights (most are bidirectional):
# 1. Prague and Budapest      -> (Prague, Budapest)            => (4, 3)
# 2. Vienna and Rome          -> (Vienna, Rome)                => (6, 2)
# 3. Prague and Stockholm     -> (Prague, Stockholm)           => (4, 0)
# 4. Prague and Tallinn       -> (Prague, Tallinn)             => (4, 1)
# 5. Stockholm and Vienna     -> (Stockholm, Vienna)           => (0, 6)
# 6. Tallinn and Stockholm    -> (Tallinn, Stockholm)          => (1, 0)
# 7. Vienna and Budapest      -> (Vienna, Budapest)            => (6, 3)
# 8. Krakow and Vienna        -> (Krakow, Vienna)              => (5, 6)
# 9. Prague and Vienna        -> (Prague, Vienna)              => (4, 6)
# 10. Prague and Rome         -> (Prague, Rome)                => (4, 2)
# 11. Rome and Budapest       -> (Rome, Budapest)              => (2, 3)
# 12. Krakow and Stockholm    -> (Krakow, Stockholm)           => (5, 0)
# 13. Stockholm and Rome      -> (Stockholm, Rome)             => (0, 2)
# 14. Krakow and Prague       -> (Krakow, Prague)              => (5, 4)

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

bidir(4, 3)  # Prague and Budapest
bidir(6, 2)  # Vienna and Rome
bidir(4, 0)  # Prague and Stockholm
bidir(4, 1)  # Prague and Tallinn
bidir(0, 6)  # Stockholm and Vienna
bidir(1, 0)  # Tallinn and Stockholm
bidir(6, 3)  # Vienna and Budapest
bidir(5, 6)  # Krakow and Vienna
bidir(4, 6)  # Prague and Vienna
bidir(4, 2)  # Prague and Rome
bidir(2, 3)  # Rome and Budapest
bidir(5, 0)  # Krakow and Stockholm
bidir(0, 2)  # Stockholm and Rome
bidir(5, 4)  # Krakow and Prague

# Set up Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define an ordering variable: a permutation of the city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each slot in the itinerary.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, the departure day equals arrival + (duration - 1)
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day:
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 14.
s.add(departures[n-1] == 14)

# Event-specific time constraints:
# Stockholm (city 0): meet friend between day 6 and day 9 → force arrival = 6.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 6, True))
# Tallinn (city 1): meet friends between day 4 and day 6 → force arrival = 4.
for i in range(n):
    s.add(If(order[i] == 1, arrivals[i] == 4, True))
# Rome (city 2): wedding between day 10 and day 13 → force arrival = 10.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 10, True))

# Connectivity constraints:
# Each consecutive pair of cities in the itinerary must be connected by an allowed direct flight.
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
        city = cities[m.evaluate(order[i]).as_long()]
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {city:10s}: [{a_day}, {d_day}]")
else:
    print("No solution found")