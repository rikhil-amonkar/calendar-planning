from z3 import *

# Cities and durations:
# 0: Salzburg   (4 days)
# 1: Stockholm  (2 days)
# 2: Venice     (5 days) – Annual show from day 1 to day 5, so force arrival = 1.
# 3: Frankfurt  (4 days)
# 4: Florence   (4 days)
# 5: Barcelona  (2 days)
# 6: Stuttgart  (3 days)
#
# Total raw days = 4 + 2 + 5 + 4 + 4 + 2 + 3 = 24.
# With 6 transitions (each consecutive visit shares one day), the entire trip lasts:
#   24 - 6 = 18 days.
cities = ["Salzburg", "Stockholm", "Venice", "Frankfurt", "Florence", "Barcelona", "Stuttgart"]
durations = [4, 2, 5, 4, 4, 2, 3]

# Allowed direct flights (bidirectional):
# 1. Barcelona and Frankfurt     → (Barcelona, Frankfurt)
# 2. Florence and Frankfurt      → (Florence, Frankfurt)
# 3. Stockholm and Barcelona     → (Stockholm, Barcelona)
# 4. Barcelona and Florence      → (Barcelona, Florence)
# 5. Venice and Barcelona        → (Venice, Barcelona)
# 6. Stuttgart and Barcelona     → (Stuttgart, Barcelona)
# 7. Frankfurt and Salzburg      → (Frankfurt, Salzburg)
# 8. Stockholm and Frankfurt     → (Stockholm, Frankfurt)
# 9. Stuttgart and Stockholm     → (Stuttgart, Stockholm)
# 10. Stuttgart and Frankfurt    → (Stuttgart, Frankfurt)
# 11. Venice and Stuttgart       → (Venice, Stuttgart)
# 12. Venice and Frankfurt       → (Venice, Frankfurt)

allowed_flights = []
def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

bidir(5, 3)  # Barcelona <-> Frankfurt
bidir(4, 3)  # Florence <-> Frankfurt
bidir(1, 5)  # Stockholm <-> Barcelona
bidir(5, 4)  # Barcelona <-> Florence
bidir(2, 5)  # Venice <-> Barcelona
bidir(6, 5)  # Stuttgart <-> Barcelona
bidir(3, 0)  # Frankfurt <-> Salzburg
bidir(1, 3)  # Stockholm <-> Frankfurt
bidir(6, 1)  # Stuttgart <-> Stockholm
bidir(6, 3)  # Stuttgart <-> Frankfurt
bidir(2, 6)  # Venice <-> Stuttgart
bidir(2, 3)  # Venice <-> Frankfurt

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Create a permutation variable representing the order in which the cities are visited.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each city visit slot.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, compute the departure day based on the city's duration:
# departure = arrival + duration - 1
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share a transit day: arrival of next equals departure of previous.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 18.
s.add(departures[n-1] == 18)

# Event-specific constraints:
# Venice (city index 2): Annual show from day 1 to 5, so force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 1, True))

# Connectivity constraints:
# Each consecutive pair in the itinerary must be connected by a direct flight (direction does not matter).
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