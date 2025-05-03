from z3 import *

# Cities with indices, durations, and event constraints:
# 0: Vienna      (2 days) – Workshop in Vienna between day 5 and 6 → force arrival = 5.
# 1: Santorini   (4 days) – Meet a friend in Santorini between day 2 and 5 → force arrival = 2.
# 2: Istanbul    (3 days)
# 3: Copenhagen  (5 days) – Meet friends at Copenhagen between day 6 and 10 → force arrival = 6.
# 4: Dubrovnik   (3 days)
# 5: Budapest    (2 days)
# 6: Venice      (2 days)
#
# Total raw days = 2 + 4 + 3 + 5 + 3 + 2 + 2 = 21.
# With 6 transitions (overlap of one day each between consecutive visits),
# overall trip length = 21 - 6 = 15 days.
cities = ["Vienna", "Santorini", "Istanbul", "Copenhagen", "Dubrovnik", "Budapest", "Venice"]
durations = [2, 4, 3, 5, 3, 2, 2]

# Allowed direct flights:
# 1. Venice and Copenhagen       -> bidir: (Venice, Copenhagen)              => (6,3)
# 2. Santorini and Copenhagen    -> bidir: (Santorini, Copenhagen)           => (1,3)
# 3. Copenhagen and Istanbul     -> bidir: (Copenhagen, Istanbul)            => (3,2)
# 4. Istanbul and Budapest       -> bidir: (Istanbul, Budapest)              => (2,5)
# 5. Vienna and Istanbul         -> bidir: (Vienna, Istanbul)                => (0,2)
# 6. Copenhagen and Budapest     -> bidir: (Copenhagen, Budapest)            => (3,5)
# 7. from Dubrovnik to Istanbul  -> one-way: (Dubrovnik, Istanbul)          => (4,2)
# 8. Vienna and Budapest         -> bidir: (Vienna, Budapest)                => (0,5)
# 9. Venice and Santorini        -> bidir: (Venice, Santorini)               => (6,1)
# 10. Copenhagen and Dubrovnik   -> bidir: (Copenhagen, Dubrovnik)           => (3,4)
# 11. Santorini and Vienna       -> bidir: (Santorini, Vienna)               => (1,0)
# 12. Venice and Istanbul        -> bidir: (Venice, Istanbul)                => (6,2)
# 13. Vienna and Copenhagen      -> bidir: (Vienna, Copenhagen)              => (0,3)
# 14. Vienna and Dubrovnik       -> bidir: (Vienna, Dubrovnik)               => (0,4)
# 15. Venice and Vienna          -> bidir: (Venice, Vienna)                  => (6,0)

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Venice <-> Copenhagen
bidir(6, 3)
# 2. Santorini <-> Copenhagen
bidir(1, 3)
# 3. Copenhagen <-> Istanbul
bidir(3, 2)
# 4. Istanbul <-> Budapest
bidir(2, 5)
# 5. Vienna <-> Istanbul
bidir(0, 2)
# 6. Copenhagen <-> Budapest
bidir(3, 5)
# 7. One-way: from Dubrovnik to Istanbul
allowed_flights.append((4, 2))
# 8. Vienna <-> Budapest
bidir(0, 5)
# 9. Venice <-> Santorini
bidir(6, 1)
# 10. Copenhagen <-> Dubrovnik
bidir(3, 4)
# 11. Santorini <-> Vienna
bidir(1, 0)
# 12. Venice <-> Istanbul
bidir(6, 2)
# 13. Vienna <-> Copenhagen
bidir(0, 3)
# 14. Vienna <-> Dubrovnik
bidir(0, 4)
# 15. Venice <-> Vienna
bidir(6, 0)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the visitation order as a permutation of city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, the departure day = arrival day + (duration - 1).
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: the next city's arrival equals the previous city's departure.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 15.
s.add(departures[n-1] == 15)

# Event-specific constraints:
# Vienna (city 0): workshop between day 5 and 6 → force arrival = 5.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 5, True))
# Santorini (city 1): meet a friend between day 2 and 5 → force arrival = 2.
for i in range(n):
    s.add(If(order[i] == 1, arrivals[i] == 2, True))
# Copenhagen (city 3): meet friends between day 6 and 10 → force arrival = 6.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 6, True))

# Connectivity constraints: each consecutive pair must be connected by a direct flight.
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
        city = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city]:11s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")