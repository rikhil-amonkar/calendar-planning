from z3 import *

# City indices and durations:
# 0: Warsaw   (5 days) – Meet your friends between day 11 and 15 → force arrival = 11.
# 1: Florence (2 days) – Workshop between day 21 and 22 → force arrival = 21.
# 2: Helsinki (4 days)
# 3: Krakow   (4 days) – Meet a friend between day 8 and 11 → force arrival = 8.
# 4: Vienna   (5 days)
# 5: Tallinn  (5 days)
# 6: Naples   (3 days)
#
# Total raw days = 5 + 2 + 4 + 4 + 5 + 5 + 3 = 28.
# With 6 overlaps (one per transition for 7 visits), overall trip length = 28 - 6 = 22 days.

cities = ["Warsaw", "Florence", "Helsinki", "Krakow", "Vienna", "Tallinn", "Naples"]
durations = [5, 2, 4, 4, 5, 5, 3]

# Allowed direct flights (bidirectional unless noted):
# 1. Naples and Vienna
# 2. Warsaw and Naples
# 3. Tallinn and Warsaw
# 4. Helsinki and Krakow
# 5. Helsinki and Warsaw
# 6. Warsaw and Vienna
# 7. Vienna and Florence
# 8. Helsinki and Vienna
# 9. Krakow and Vienna
# 10. Helsinki and Naples
# 11. Krakow and Warsaw
# 12. Tallinn and Helsinki

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# Naples <-> Vienna
add_bidirectional(6, 4)
# Warsaw <-> Naples
add_bidirectional(0, 6)
# Tallinn <-> Warsaw
add_bidirectional(5, 0)
# Helsinki <-> Krakow
add_bidirectional(2, 3)
# Helsinki <-> Warsaw
add_bidirectional(2, 0)
# Warsaw <-> Vienna
add_bidirectional(0, 4)
# Vienna <-> Florence
add_bidirectional(4, 1)
# Helsinki <-> Vienna
add_bidirectional(2, 4)
# Krakow <-> Vienna
add_bidirectional(3, 4)
# Helsinki <-> Naples
add_bidirectional(2, 6)
# Krakow <-> Warsaw
add_bidirectional(3, 0)
# Tallinn <-> Helsinki
add_bidirectional(5, 2)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Create a permutation (order) for the visits.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit position i, if city c is visited then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: The arrival of the next city is exactly the departure day of the previous city.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 22.
s.add(departures[n-1] == 22)

# Event-specific constraints:
# Warsaw (index 0): meet friends between day 11 and 15 → force arrival = 11.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 11, True))
# Florence (index 1): workshop between day 21 and 22 → force arrival = 21.
for i in range(n):
    s.add(If(order[i] == 1, arrivals[i] == 21, True))
# Krakow (index 3): meet a friend between day 8 and 11 → force arrival = 8.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 8, True))

# Connectivity constraints:
# Each consecutive pair of cities in the itinerary must be connected by an allowed direct flight.
for i in range(n-1):
    connection_options = []
    for (frm, to) in allowed_flights:
        connection_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(connection_options))

# Solve the model and display the itinerary.
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