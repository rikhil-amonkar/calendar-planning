from z3 import *

# City indices and durations:
# 0: Geneva    (4 days)
# 1: Helsinki  (3 days)
# 2: Vilnius   (2 days) – Meet a friend in Vilnius between day 13 and 14 → force arrival = 13.
# 3: Salzburg  (4 days)
# 4: Hamburg   (5 days)
# 5: Stuttgart (2 days)
# 6: Vienna    (4 days) – Annual show in Vienna between day 14 and 17 → force arrival = 14.
#
# Total raw days = 4 + 3 + 2 + 4 + 5 + 2 + 4 = 24.
# With 6 overlaps (between 7 consecutive visits), overall trip length = 24 - 6 = 18 days.

cities = ["Geneva", "Helsinki", "Vilnius", "Salzburg", "Hamburg", "Stuttgart", "Vienna"]
durations = [4, 3, 2, 4, 5, 2, 4]

# Allowed direct flights:
# 1. Salzburg and Hamburg
# 2. from Hamburg to Geneva (one-way)
# 3. Hamburg and Vienna
# 4. Vienna and Stuttgart
# 5. Hamburg and Helsinki
# 6. Helsinki and Vilnius
# 7. Vilnius and Vienna
# 8. Geneva and Helsinki
# 9. Helsinki and Vienna
# 10. Hamburg and Stuttgart
# 11. Geneva and Vienna

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Salzburg <-> Hamburg
add_bidirectional(3, 4)
# 2. One-way: Hamburg -> Geneva
allowed_flights.append((4, 0))
# 3. Hamburg <-> Vienna
add_bidirectional(4, 6)
# 4. Vienna <-> Stuttgart
add_bidirectional(6, 5)
# 5. Hamburg <-> Helsinki
add_bidirectional(4, 1)
# 6. Helsinki <-> Vilnius
add_bidirectional(1, 2)
# 7. Vilnius <-> Vienna
add_bidirectional(2, 6)
# 8. Geneva <-> Helsinki
add_bidirectional(0, 1)
# 9. Helsinki <-> Vienna
add_bidirectional(1, 6)
# 10. Hamburg <-> Stuttgart
add_bidirectional(4, 5)
# 11. Geneva <-> Vienna
add_bidirectional(0, 6)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Model the itinerary as a permutation of the cities.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Create arrival and departure day variables for each visit in the itinerary.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the city c is visited then its departure is given by:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: the arrival of the next city equals the departure day of the previous one.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 18.
s.add(departures[n-1] == 18)

# Event-specific constraints:
# Vilnius (index 2): Meet a friend between day 13 and 14 → force arrival = 13.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 13, True))
# Vienna (index 6): Annual show between day 14 and 17 → force arrival = 14.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 14, True))

# Connectivity constraints:
# Each consecutive pair of visited cities must have a direct flight connection.
for i in range(n-1):
    connection_options = []
    for (frm, to) in allowed_flights:
        connection_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(connection_options))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:9s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")