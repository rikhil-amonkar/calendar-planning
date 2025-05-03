from z3 import *

# City indices and durations:
# 0: Santorini (2 days) – Visit relatives in Santorini between day 9 and day 10 → force arrival = 9.
# 1: Athens     (3 days)
# 2: Valencia   (2 days) – Conference in Valencia between day 13 and day 14 → force arrival = 13.
# 3: Venice     (4 days)
# 4: Madrid     (4 days)
# 5: Helsinki   (5 days)
# 6: Istanbul   (2 days) – Workshop in Istanbul between day 5 and day 6 → force arrival = 5.
#
# Total raw days = 2 + 3 + 2 + 4 + 4 + 5 + 2 = 22.
# With 6 overlaps between visits (7 cities), overall trip length = 22 - 6 = 16 days.

cities = ["Santorini", "Athens", "Valencia", "Venice", "Madrid", "Helsinki", "Istanbul"]
durations = [2, 3, 2, 4, 4, 5, 2]

# Allowed direct flights:
# 1. Santorini and Madrid
# 2. Venice and Santorini
# 3. Venice and Athens
# 4. Istanbul and Valencia
# 5. Helsinki and Venice
# 6. Helsinki and Madrid
# 7. Madrid and Valencia
# 8. Istanbul and Madrid
# 9. Santorini and Athens
# 10. Helsinki and Istanbul
# 11. Istanbul and Athens
# 12. Istanbul and Venice
# 13. from Valencia to Athens (one-way from Valencia -> Athens)
# 14. Madrid and Athens
# 15. Venice and Madrid

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Santorini <-> Madrid
add_bidirectional(0, 4)
# 2. Venice <-> Santorini
add_bidirectional(3, 0)
# 3. Venice <-> Athens
add_bidirectional(3, 1)
# 4. Istanbul <-> Valencia
add_bidirectional(6, 2)
# 5. Helsinki <-> Venice
add_bidirectional(5, 3)
# 6. Helsinki <-> Madrid
add_bidirectional(5, 4)
# 7. Madrid <-> Valencia
add_bidirectional(4, 2)
# 8. Istanbul <-> Madrid
add_bidirectional(6, 4)
# 9. Santorini <-> Athens
add_bidirectional(0, 1)
# 10. Helsinki <-> Istanbul
add_bidirectional(5, 6)
# 11. Istanbul <-> Athens
add_bidirectional(6, 1)
# 12. Istanbul <-> Venice
add_bidirectional(6, 3)
# 13. One-way from Valencia to Athens
allowed_flights.append((2, 1))
# 14. Madrid <-> Athens
add_bidirectional(4, 1)
# 15. Venice <-> Madrid
add_bidirectional(3, 4)

# Set up Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Order: permutation of 0..6 representing the sequence of visits.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit at position i, departure time is computed by:
# departure = arrival + duration - 1 (depending on the city visited at that slot).
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: next arrival equals previous departure.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 16.
s.add(departures[n-1] == 16)

# Event-specific constraints:
# Santorini (index 0): visit relatives between day 9 and day 10 → force arrival = 9.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 9, True))
# Valencia (index 2): conference between day 13 and day 14 → force arrival = 13.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 13, True))
# Istanbul (index 6): workshop between day 5 and day 6 → force arrival = 5.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 5, True))

# Connectivity constraints:
# Each consecutive pair of cities must be linked by an allowed direct flight.
for i in range(n-1):
    conn_options = []
    for (frm, to) in allowed_flights:
        conn_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(conn_options))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        itinerary.append((cities[city_index], arr_day, dep_day))
        print(f"  {cities[city_index]:10s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")