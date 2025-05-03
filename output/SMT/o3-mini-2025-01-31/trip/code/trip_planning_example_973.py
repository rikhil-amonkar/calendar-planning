from z3 import *

# Cities with durations and event constraints:
# 0: Paris      (2 days) – Meet a friend in Paris between day 1 and 2 → force arrival = 1.
# 1: Venice     (5 days)
# 2: Tallinn    (2 days)
# 3: Edinburgh  (3 days) – Workshop in Edinburgh between day 2 and 4 → force arrival = 2.
# 4: Helsinki   (5 days)
# 5: Vilnius    (4 days)
# 6: Naples     (2 days)
#
# Total raw days = 2 + 5 + 2 + 3 + 5 + 4 + 2 = 23.
# There are 6 overlapping transit days, so overall trip length = 23 - 6 = 17 days.

cities = ["Paris", "Venice", "Tallinn", "Edinburgh", "Helsinki", "Vilnius", "Naples"]
durations = [2, 5, 2, 3, 5, 4, 2]

# Allowed direct flights:
# 1. Naples and Helsinki       -> (Naples, Helsinki)       => (6, 4)
# 2. Venice and Helsinki       -> (Venice, Helsinki)       => (1, 4)
# 3. Paris and Helsinki        -> (Paris, Helsinki)        => (0, 4)
# 4. Paris and Vilnius         -> (Paris, Vilnius)         => (0, 5)
# 5. from Tallinn to Vilnius   -> one-way: (Tallinn, Vilnius) => (2, 5)
# 6. Paris and Naples          -> (Paris, Naples)          => (0, 6)
# 7. Edinburgh and Venice      -> (Edinburgh, Venice)      => (3, 1)
# 8. Paris and Venice          -> (Paris, Venice)          => (0, 1)
# 9. Paris and Tallinn         -> (Paris, Tallinn)         => (0, 2)
# 10. Helsinki and Tallinn     -> (Helsinki, Tallinn)      => (4, 2)
# 11. Venice and Naples        -> (Venice, Naples)         => (1, 6)
# 12. Helsinki and Vilnius     -> (Helsinki, Vilnius)      => (4, 5)
# 13. Paris and Edinburgh      -> (Paris, Edinburgh)       => (0, 3)
# 14. Edinburgh and Helsinki   -> (Edinburgh, Helsinki)    => (3, 4)

# Build allowed flights list.
allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Naples <-> Helsinki
bidir(6, 4)
# 2. Venice <-> Helsinki
bidir(1, 4)
# 3. Paris <-> Helsinki
bidir(0, 4)
# 4. Paris <-> Vilnius
bidir(0, 5)
# 5. One-way: from Tallinn to Vilnius (only (2,5) allowed)
allowed_flights.append((2, 5))
# 6. Paris <-> Naples
bidir(0, 6)
# 7. Edinburgh <-> Venice
bidir(3, 1)
# 8. Paris <-> Venice
bidir(0, 1)
# 9. Paris <-> Tallinn
bidir(0, 2)
# 10. Helsinki <-> Tallinn
bidir(4, 2)
# 11. Venice <-> Naples
bidir(1, 6)
# 12. Helsinki <-> Vilnius
bidir(4, 5)
# 13. Paris <-> Edinburgh
bidir(0, 3)
# 14. Edinburgh <-> Helsinki
bidir(3, 4)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the permutation for the order of visiting cities.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the city with index c is visited, then:
# departure[i] = arrival[i] + duration[c] - 1
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Sequential visits: The next visit starts on the same day as the previous visit ends.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 17.
s.add(departures[n-1] == 17)

# Event-specific constraints:
# Paris (city 0): meet a friend between day 1 and 2 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 1, True))
# Edinburgh (city 3): workshop between day 2 and 4 → force arrival = 2.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 2, True))

# Connectivity constraints:
# Each consecutive pair of visited cities must have a direct flight.
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
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:10s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")