from z3 import *

# City indices and durations:
# 0: Stuttgart  (3 days) – Visit relatives in Stuttgart between day 6 and day 8 → force arrival = 6.
# 1: Manchester (5 days)
# 2: Vilnius    (5 days) – Workshop in Vilnius between day 17 and day 21 → force arrival = 17.
# 3: Seville    (2 days)
# 4: Salzburg   (4 days)
# 5: Istanbul   (4 days) – Annual show in Istanbul from day 8 to day 11 → force arrival = 8.
# 6: Berlin     (4 days)
#
# Sum of raw durations = 3 + 5 + 5 + 2 + 4 + 4 + 4 = 27.
# With 6 overlapping transit days (one less than the number of cities), the overall trip length = 27 - 6 = 21 days.

cities = ["Stuttgart", "Manchester", "Vilnius", "Seville", "Salzburg", "Istanbul", "Berlin"]
durations = [3, 5, 5, 2, 4, 4, 4]

# Allowed direct flights (bidirectional):
# 1. Berlin and Vilnius      -> (Berlin, Vilnius): (6,2)
# 2. Manchester and Berlin   -> (Manchester, Berlin): (1,6)
# 3. Manchester and Stuttgart-> (Manchester, Stuttgart): (1,0)
# 4. Seville and Manchester  -> (Seville, Manchester): (3,1)
# 5. Salzburg and Berlin     -> (Salzburg, Berlin): (4,6)
# 6. Stuttgart and Istanbul  -> (Stuttgart, Istanbul): (0,5)
# 7. Istanbul and Vilnius    -> (Istanbul, Vilnius): (5,2)
# 8. Manchester and Istanbul -> (Manchester, Istanbul): (1,5)
# 9. Istanbul and Salzburg   -> (Istanbul, Salzburg): (5,4)
# 10. Stuttgart and Berlin    -> (Stuttgart, Berlin): (0,6)
# 11. Istanbul and Berlin     -> (Istanbul, Berlin): (5,6)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

add_bidirectional(6, 2)  # Berlin <-> Vilnius
add_bidirectional(1, 6)  # Manchester <-> Berlin
add_bidirectional(1, 0)  # Manchester <-> Stuttgart
add_bidirectional(3, 1)  # Seville <-> Manchester
add_bidirectional(4, 6)  # Salzburg <-> Berlin
add_bidirectional(0, 5)  # Stuttgart <-> Istanbul
add_bidirectional(5, 2)  # Istanbul <-> Vilnius
add_bidirectional(1, 5)  # Manchester <-> Istanbul
add_bidirectional(5, 4)  # Istanbul <-> Salzburg
add_bidirectional(0, 6)  # Stuttgart <-> Berlin
add_bidirectional(5, 6)  # Istanbul <-> Berlin

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# The itinerary is modeled as a permutation of cities.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit, if city c is visited at position i then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: the arrival day of the next city equals the departure day of the previous city.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must complete on day 21.
s.add(departures[n-1] == 21)

# Event-specific constraints:
# Stuttgart (index 0): visit relatives between day 6 and 8 → force arrival = 6.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 6, True))
# Istanbul (index 5): annual show between day 8 and 11 → force arrival = 8.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 8, True))
# Vilnius (index 2): workshop between day 17 and 21 → force arrival = 17.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 17, True))

# Connectivity constraints:
# Each consecutive pair of visited cities must be connected by a direct flight.
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
        c_index = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[c_index]:12s}: [{a_day}, {d_day}]")
else:
    print("No solution found")