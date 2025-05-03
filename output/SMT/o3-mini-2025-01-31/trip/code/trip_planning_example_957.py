from z3 import *

# Cities with indices, durations and event constraints:
# 0: Salzburg   (4 days)
# 1: Frankfurt  (5 days)
# 2: Naples     (3 days) – Annual show between day 5 and day 7 ⇒ force arrival = 5.
# 3: Oslo       (3 days)
# 4: Riga       (5 days)
# 5: Valencia   (5 days)
# 6: Stockholm  (3 days) – Wedding between day 9 and day 11 ⇒ force arrival = 9.
#
# Total raw days = 4 + 5 + 3 + 3 + 5 + 5 + 3 = 28.
# There are 6 transitions (shared days), so overall trip length = 28 - 6 = 22 days.
cities = ["Salzburg", "Frankfurt", "Naples", "Oslo", "Riga", "Valencia", "Stockholm"]
durations = [4, 5, 3, 3, 5, 5, 3]

# Define allowed direct flights (bidirectional unless specified otherwise):
# 1. Naples and Frankfurt      -> (Naples, Frankfurt): (2, 1)
# 2. Naples and Oslo           -> (Naples, Oslo): (2, 3)
# 3. Stockholm and Frankfurt   -> (Stockholm, Frankfurt): (6, 1)
# 4. Frankfurt and Salzburg    -> (Frankfurt, Salzburg): (1, 0)
# 5. Oslo and Frankfurt        -> (Oslo, Frankfurt): (3, 1)
# 6. Stockholm and Riga        -> (Stockholm, Riga): (6, 4)
# 7. Riga and Frankfurt        -> (Riga, Frankfurt): (4, 1)
# 8. Oslo and Riga             -> (Oslo, Riga): (3, 4)
# 9. Oslo and Stockholm        -> (Oslo, Stockholm): (3, 6)
# 10. Valencia and Naples      -> (Valencia, Naples): (5, 2)
# 11. Valencia and Frankfurt   -> (Valencia, Frankfurt): (5, 1)
allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

bidir(2, 1)  # Naples <-> Frankfurt
bidir(2, 3)  # Naples <-> Oslo
bidir(6, 1)  # Stockholm <-> Frankfurt
bidir(1, 0)  # Frankfurt <-> Salzburg
bidir(3, 1)  # Oslo <-> Frankfurt
bidir(6, 4)  # Stockholm <-> Riga
bidir(4, 1)  # Riga <-> Frankfurt
bidir(3, 4)  # Oslo <-> Riga
bidir(3, 6)  # Oslo <-> Stockholm
bidir(5, 2)  # Valencia <-> Naples
bidir(5, 1)  # Valencia <-> Frankfurt

# Set up the Z3 solver.
s = Solver()
n = len(cities)

# Define the visitation order as a permutation of city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each city visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit i, departure = arrival + (duration - 1)
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share a transit day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 22.
s.add(departures[n-1] == 22)

# Event-specific time constraints:
# Naples (city 2): annual show between day 5 and day 7, force arrival = 5.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 5, True))
# Stockholm (city 6): wedding between day 9 and day 11, force arrival = 9.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 9, True))

# Connectivity constraints:
# Each consecutive pair of cities in the itinerary must be connected by a direct flight.
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