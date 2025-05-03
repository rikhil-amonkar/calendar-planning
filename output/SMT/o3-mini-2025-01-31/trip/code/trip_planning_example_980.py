from z3 import *

# City indices and durations:
# 0: Athens      (4 days)
# 1: Edinburgh   (3 days)
# 2: Manchester  (5 days) – Workshop in Manchester between day 15 and 19 → force arrival = 15.
# 3: Berlin      (5 days)
# 4: Warsaw      (5 days) – Wedding in Warsaw between day 6 and 10 → force arrival = 6.
# 5: Seville     (5 days)
# 6: Riga        (2 days) – Meet a friend in Riga between day 10 and 11 → force arrival = 10.
#
# Total raw days = 4 + 3 + 5 + 5 + 5 + 5 + 2 = 29.
# There are 6 overlaps when transitioning between 7 cities,
# so overall trip length = 29 - 6 = 23 days.

cities = ["Athens", "Edinburgh", "Manchester", "Berlin", "Warsaw", "Seville", "Riga"]
durations = [4, 3, 5, 5, 5, 5, 2]

# Allowed direct flights:
# 1. Riga and Berlin         -> bidirectional: (Riga, Berlin)          => (6,3)
# 2. Warsaw and Berlin       -> bidirectional: (Warsaw, Berlin)        => (4,3)
# 3. Berlin and Manchester   -> bidirectional: (Berlin, Manchester)    => (3,2)
# 4. Riga and Manchester     -> bidirectional: (Riga, Manchester)      => (6,2)
# 5. Athens and Manchester   -> bidirectional: (Athens, Manchester)    => (0,2)
# 6. Edinburgh and Seville   -> bidirectional: (Edinburgh, Seville)      => (1,5)
# 7. Warsaw and Riga         -> bidirectional: (Warsaw, Riga)          => (4,6)
# 8. Athens and Warsaw       -> bidirectional: (Athens, Warsaw)        => (0,4)
# 9. Edinburgh and Riga      -> bidirectional: (Edinburgh, Riga)         => (1,6)
# 10. Edinburgh and Athens   -> bidirectional: (Edinburgh, Athens)      => (1,0)
# 11. Edinburgh and Berlin   -> bidirectional: (Edinburgh, Berlin)      => (1,3)
# 12. Athens and Berlin      -> bidirectional: (Athens, Berlin)         => (0,3)
# 13. Manchester and Seville -> bidirectional: (Manchester, Seville)    => (2,5)
# 14. from Athens to Riga     -> one-way: (Athens -> Riga)               => (0,6)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Riga <-> Berlin:
add_bidirectional(6, 3)
# 2. Warsaw <-> Berlin:
add_bidirectional(4, 3)
# 3. Berlin <-> Manchester:
add_bidirectional(3, 2)
# 4. Riga <-> Manchester:
add_bidirectional(6, 2)
# 5. Athens <-> Manchester:
add_bidirectional(0, 2)
# 6. Edinburgh <-> Seville:
add_bidirectional(1, 5)
# 7. Warsaw <-> Riga:
add_bidirectional(4, 6)
# 8. Athens <-> Warsaw:
add_bidirectional(0, 4)
# 9. Edinburgh <-> Riga:
add_bidirectional(1, 6)
# 10. Edinburgh <-> Athens:
add_bidirectional(1, 0)
# 11. Edinburgh <-> Berlin:
add_bidirectional(1, 3)
# 12. Athens <-> Berlin:
add_bidirectional(0, 3)
# 13. Manchester <-> Seville:
add_bidirectional(2, 5)
# 14. One-way from Athens to Riga:
allowed_flights.append((0, 6))

# Set up the Z3 solver
s = Solver()
n = len(cities)  # 7 cities

# Define the visitation order as a permutation of the cities.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if city c is visited then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: The next visit's arrival equals the previous visit's departure.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 23.
s.add(departures[n-1] == 23)

# Event-specific constraints:
# Manchester (city index 2): Workshop between day 15 and day 19 → force arrival = 15.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 15, True))
# Warsaw (city index 4): Wedding between day 6 and day 10 → force arrival = 6.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 6, True))
# Riga (city index 6): Meet friend between day 10 and day 11 → force arrival = 10.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 10, True))

# Connectivity constraints:
# Each consecutive pair of visited cities must be connected by a direct flight.
for i in range(n - 1):
    connection_options = []
    for (frm, to) in allowed_flights:
        connection_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*connection_options))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_idx]:10s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")