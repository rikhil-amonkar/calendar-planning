from z3 import *

# City indices and durations:
# 0: Riga      (2 days)
# 1: Frankfurt (3 days)
# 2: Amsterdam (2 days) – Meet a friend in Amsterdam between day 2 and 3 → force arrival = 2.
# 3: Vilnius   (5 days) – Attend a workshop in Vilnius between day 7 and 11 → force arrival = 7.
# 4: London    (2 days)
# 5: Stockholm (3 days) – Wedding in Stockholm between day 13 and 15 → force arrival = 13.
# 6: Bucharest (4 days)
#
# Total raw days = 2 + 3 + 2 + 5 + 2 + 3 + 4 = 21.
# With 6 overlaps (between 7 visits) the overall trip length = 21 - 6 = 15 days.

cities = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]
durations = [2, 3, 2, 5, 2, 3, 4]

# Allowed direct flights:
# 1. London and Amsterdam                  (London<->Amsterdam) -> (4,2) and (2,4)
# 2. Vilnius and Frankfurt                  (Vilnius<->Frankfurt) -> (3,1) and (1,3)
# 3. from Riga to Vilnius                   (one-way) -> (0,3)
# 4. Riga and Stockholm                     (Riga<->Stockholm) -> (0,5) and (5,0)
# 5. London and Bucharest                   (London<->Bucharest) -> (4,6) and (6,4)
# 6. Amsterdam and Stockholm                (Amsterdam<->Stockholm) -> (2,5) and (5,2)
# 7. Amsterdam and Frankfurt                (Amsterdam<->Frankfurt) -> (2,1) and (1,2)
# 8. Frankfurt and Stockholm                (Frankfurt<->Stockholm) -> (1,5) and (5,1)
# 9. Bucharest and Riga                     (Bucharest<->Riga) -> (6,0) and (0,6)
# 10. Amsterdam and Riga                    (Amsterdam<->Riga) -> (2,0) and (0,2)
# 11. Amsterdam and Bucharest               (Amsterdam<->Bucharest) -> (2,6) and (6,2)
# 12. Riga and Frankfurt                    (Riga<->Frankfurt) -> (0,1) and (1,0)
# 13. Bucharest and Frankfurt               (Bucharest<->Frankfurt) -> (6,1) and (1,6)
# 14. London and Frankfurt                  (London<->Frankfurt) -> (4,1) and (1,4)
# 15. London and Stockholm                  (London<->Stockholm) -> (4,5) and (5,4)
# 16. Amsterdam and Vilnius                 (Amsterdam<->Vilnius) -> (2,3) and (3,2)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a,b))
    allowed_flights.append((b,a))

# 1. London <-> Amsterdam
add_bidirectional(4, 2)
# 2. Vilnius <-> Frankfurt
add_bidirectional(3, 1)
# 3. from Riga to Vilnius (one-way)
allowed_flights.append((0, 3))
# 4. Riga <-> Stockholm
add_bidirectional(0, 5)
# 5. London <-> Bucharest
add_bidirectional(4, 6)
# 6. Amsterdam <-> Stockholm
add_bidirectional(2, 5)
# 7. Amsterdam <-> Frankfurt
add_bidirectional(2, 1)
# 8. Frankfurt <-> Stockholm
add_bidirectional(1, 5)
# 9. Bucharest <-> Riga
add_bidirectional(6, 0)
# 10. Amsterdam <-> Riga
add_bidirectional(2, 0)
# 11. Amsterdam <-> Bucharest
add_bidirectional(2, 6)
# 12. Riga <-> Frankfurt
add_bidirectional(0, 1)
# 13. Bucharest <-> Frankfurt
add_bidirectional(6, 1)
# 14. London <-> Frankfurt
add_bidirectional(4, 1)
# 15. London <-> Stockholm
add_bidirectional(4, 5)
# 16. Amsterdam <-> Vilnius
add_bidirectional(2, 3)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# The itinerary is modeled as a permutation of the cities (each city is visited exactly once).
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit position i, if city c is visited then its departure equals arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: the arrival of the next city equals the departure of the previous city.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 15.
s.add(departures[n-1] == 15)

# Event-specific constraints:
# Amsterdam (city index 2): Meet a friend between day 2 and 3 → force arrival = 2.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 2, True))
# Vilnius (city index 3): Workshop between day 7 and 11 → force arrival = 7.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 7, True))
# Stockholm (city index 5): Wedding between day 13 and 15 → force arrival = 13.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 13, True))

# Connectivity constraints:
# For each consecutive pair of cities in the itinerary, there should be a direct flight.
for i in range(n-1):
    connection_options = []
    for (frm, to) in allowed_flights:
        connection_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(connection_options))

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