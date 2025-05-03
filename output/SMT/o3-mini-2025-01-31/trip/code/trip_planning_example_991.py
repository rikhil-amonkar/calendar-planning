from z3 import *

# City indices and durations:
# 0: Frankfurt  (2 days)
# 1: London     (2 days)
# 2: Salzburg   (5 days)
# 3: Lyon       (4 days) – Annual show from day 2 to 5 → force arrival = 2.
# 4: Bucharest  (2 days) – Meet friends between day 5 and 6 → force arrival = 5.
# 5: Munich     (3 days) – Conference from day 6 to 8 → force arrival = 6.
# 6: Dubrovnik  (4 days)
#
# Total raw days = 2 + 2 + 5 + 4 + 2 + 3 + 4 = 22.
# With 6 overlaps between the 7 visits, overall trip length = 22 - 6 = 16 days.

cities = ["Frankfurt", "London", "Salzburg", "Lyon", "Bucharest", "Munich", "Dubrovnik"]
durations = [2, 2, 5, 4, 2, 3, 4]

# Allowed direct flights (bidirectional unless noted):
# 1. Frankfurt and Salzburg:         (0,2)
# 2. Lyon and Munich:                (3,5)
# 3. Lyon and Bucharest:             (3,4)
# 4. London and Frankfurt:           (1,0)
# 5. Munich and Frankfurt:           (5,0)
# 6. Munich and Dubrovnik:           (5,6)
# 7. London and Lyon:                (1,3)
# 8. Bucharest and Frankfurt:        (4,0)
# 9. London and Bucharest:           (1,4)
# 10. Dubrovnik and Frankfurt:       (6,0)
# 11. Lyon and Frankfurt:            (3,0)
# 12. London and Munich:             (1,5)
# 13. Bucharest and Munich:          (4,5)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

add_bidirectional(0, 2)  # Frankfurt <-> Salzburg
add_bidirectional(3, 5)  # Lyon <-> Munich
add_bidirectional(3, 4)  # Lyon <-> Bucharest
add_bidirectional(1, 0)  # London <-> Frankfurt
add_bidirectional(5, 0)  # Munich <-> Frankfurt
add_bidirectional(5, 6)  # Munich <-> Dubrovnik
add_bidirectional(1, 3)  # London <-> Lyon
add_bidirectional(4, 0)  # Bucharest <-> Frankfurt
add_bidirectional(1, 4)  # London <-> Bucharest
add_bidirectional(6, 0)  # Dubrovnik <-> Frankfurt
add_bidirectional(3, 0)  # Lyon <-> Frankfurt
add_bidirectional(1, 5)  # London <-> Munich
add_bidirectional(4, 5)  # Bucharest <-> Munich

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Create a permutation representing the order of visits.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit i: departure = arrival + duration - 1 (depending on the city visited in slot i).
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Ensure consecutive visits overlap: the arrival of the next is the same as the previous departure.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 16.
s.add(departures[n-1] == 16)

# Event-specific constraints:
# Lyon (index 3): Annual show from day 2 to 5 → force arrival = 2.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 2, True))
# Bucharest (index 4): Meet friends between day 5 and 6 → force arrival = 5.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 5, True))
# Munich (index 5): Conference from day 6 to 8 → force arrival = 6.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 6, True))

# Connectivity constraints: each consecutive pair in the itinerary must be directly connected.
for i in range(n - 1):
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
        print(f"  {cities[city_index]:12s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")