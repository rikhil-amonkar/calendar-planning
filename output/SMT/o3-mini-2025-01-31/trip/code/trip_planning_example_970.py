from z3 import *

# Cities (indices) with durations and event constraints:
# 0: Lyon      (2 days)  – Workshop in Lyon between day 4 and 5 → force arrival = 4.
# 1: Milan     (3 days)
# 2: Barcelona (2 days)
# 3: Seville   (5 days)  – Meet friend in Seville between day 6 and 10 → force arrival = 6.
# 4: Stuttgart (5 days)
# 5: Riga      (3 days)
# 6: Bucharest (2 days)
#
# Total raw days = 2 + 3 + 2 + 5 + 5 + 3 + 2 = 22.
# There are 6 overlaps between visits, so overall trip length = 22 - 6 = 16 days.

cities = ["Lyon", "Milan", "Barcelona", "Seville", "Stuttgart", "Riga", "Bucharest"]
durations = [2, 3, 2, 5, 5, 3, 2]

# Allowed direct flights (bidirectional):
# 1. Bucharest and Barcelona          -> (Bucharest, Barcelona) (6, 2)
# 2. Seville and Milan                -> (Seville, Milan)       (3, 1)
# 3. Barcelona and Seville            -> (Barcelona, Seville)   (2, 3)
# 4. Lyon and Barcelona               -> (Lyon, Barcelona)      (0, 2)
# 5. Barcelona and Milan              -> (Barcelona, Milan)     (2, 1)
# 6. Bucharest and Lyon               -> (Bucharest, Lyon)      (6, 0)
# 7. Barcelona and Stuttgart         -> (Barcelona, Stuttgart) (2, 4)
# 8. Riga and Bucharest               -> (Riga, Bucharest)      (5, 6)
# 9. Riga and Barcelona               -> (Riga, Barcelona)      (5, 2)
# 10. Milan and Stuttgart             -> (Milan, Stuttgart)     (1, 4)
# 11. Riga and Milan                  -> (Riga, Milan)          (5, 1)

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Bucharest <-> Barcelona
bidir(6, 2)
# 2. Seville <-> Milan
bidir(3, 1)
# 3. Barcelona <-> Seville
bidir(2, 3)
# 4. Lyon <-> Barcelona
bidir(0, 2)
# 5. Barcelona <-> Milan
bidir(2, 1)
# 6. Bucharest <-> Lyon
bidir(6, 0)
# 7. Barcelona <-> Stuttgart
bidir(2, 4)
# 8. Riga <-> Bucharest
bidir(5, 6)
# 9. Riga <-> Barcelona
bidir(5, 2)
# 10. Milan <-> Stuttgart
bidir(1, 4)
# 11. Riga <-> Milan
bidir(5, 1)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the order in which cities are visited as a permutation.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if city c is visited then:
# departure[i] = arrivals[i] + (durations[c] - 1)
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share one transit day:
# arrival[i+1] = departure[i]
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must end on day 16.
s.add(departures[n-1] == 16)

# Event-specific constraints:
# Lyon (city 0) – workshop between day 4 and 5 → force arrival = 4.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 4, True))
# Seville (city 3) – meet friend between day 6 and 10 → force arrival = 6.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 6, True))

# Connectivity constraints:
# Each consecutive pair of cities in the itinerary must have a direct flight.
for i in range(n - 1):
    connections = []
    for (frm, to) in allowed_flights:
        connections.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*connections))

# Solve and output the itinerary.
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