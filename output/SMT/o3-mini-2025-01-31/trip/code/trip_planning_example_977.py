from z3 import *

# City indices and durations:
# 0: Riga       (2 days)
# 1: Tallinn    (4 days) – Conference between day 15 and day 18 → force arrival = 15.
# 2: London     (3 days)
# 3: Vienna     (4 days)
# 4: Copenhagen (5 days)
# 5: Istanbul   (5 days) – Workshop between day 7 and day 11 → force arrival = 7.
# 6: Barcelona  (5 days) – Meet a friend between day 1 and day 5 → force arrival = 1.
#
# Total raw days = 2 + 4 + 3 + 4 + 5 + 5 + 5 = 28.
# With 6 overlapping transit days (each visit except the first overlaps by 1 day), 
# overall trip duration = 28 - 6 = 22 days.

cities = ["Riga", "Tallinn", "London", "Vienna", "Copenhagen", "Istanbul", "Barcelona"]
durations = [2, 4, 3, 4, 5, 5, 5]

# Allowed direct flights:
# 1. Vienna and Riga                        -> bidirectional: (Vienna, Riga)        => (3,0)
# 2. from Istanbul to Tallinn                -> one-way: (Istanbul, Tallinn)           => (5,1)
# 3. London and Vienna                        -> bidirectional: (London, Vienna)        => (2,3)
# 4. Barcelona and Istanbul                   -> bidirectional: (Barcelona, Istanbul)   => (6,5)
# 5. Barcelona and Riga                       -> bidirectional: (Barcelona, Riga)       => (6,0)
# 6. Istanbul and Riga                        -> bidirectional: (Istanbul, Riga)        => (5,0)
# 7. Vienna and Copenhagen                    -> bidirectional: (Vienna, Copenhagen)    => (3,4)
# 8. Istanbul and Vienna                      -> bidirectional: (Istanbul, Vienna)      => (5,3)
# 9. Barcelona and London                     -> bidirectional: (Barcelona, London)     => (6,2)
# 10. Riga and Copenhagen                     -> bidirectional: (Riga, Copenhagen)      => (0,4)
# 11. Tallinn and Copenhagen                  -> bidirectional: (Tallinn, Copenhagen)   => (1,4)
# 12. London and Copenhagen                   -> bidirectional: (London, Copenhagen)    => (2,4)
# 13. Barcelona and Vienna                    -> bidirectional: (Barcelona, Vienna)     => (6,3)
# 14. from Riga to Tallinn                    -> one-way: (Riga, Tallinn)               => (0,1)
# 15. Barcelona and Copenhagen                -> bidirectional: (Barcelona, Copenhagen) => (6,4)
# 16. Barcelona and Tallinn                   -> bidirectional: (Barcelona, Tallinn)    => (6,1)
# 17. London and Istanbul                     -> bidirectional: (London, Istanbul)      => (2,5)
# 18. Istanbul and Copenhagen                 -> bidirectional: (Istanbul, Copenhagen)  => (5,4)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Vienna <-> Riga
add_bidirectional(3, 0)
# 2. One-way: Istanbul -> Tallinn
allowed_flights.append((5, 1))
# 3. London <-> Vienna
add_bidirectional(2, 3)
# 4. Barcelona <-> Istanbul
add_bidirectional(6, 5)
# 5. Barcelona <-> Riga
add_bidirectional(6, 0)
# 6. Istanbul <-> Riga
add_bidirectional(5, 0)
# 7. Vienna <-> Copenhagen
add_bidirectional(3, 4)
# 8. Istanbul <-> Vienna
add_bidirectional(5, 3)
# 9. Barcelona <-> London
add_bidirectional(6, 2)
# 10. Riga <-> Copenhagen
add_bidirectional(0, 4)
# 11. Tallinn <-> Copenhagen
add_bidirectional(1, 4)
# 12. London <-> Copenhagen
add_bidirectional(2, 4)
# 13. Barcelona <-> Vienna
add_bidirectional(6, 3)
# 14. One-way: Riga -> Tallinn
allowed_flights.append((0, 1))
# 15. Barcelona <-> Copenhagen
add_bidirectional(6, 4)
# 16. Barcelona <-> Tallinn
add_bidirectional(6, 1)
# 17. London <-> Istanbul
add_bidirectional(2, 5)
# 18. Istanbul <-> Copenhagen
add_bidirectional(5, 4)

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

# For each visit, if city c is visited then:
# departure = arrival + duration[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits: next arrival equals previous departure (overlap by 1).
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 22.
s.add(departures[n-1] == 22)

# Event-specific constraints:
# Tallinn (city index 1): Conference between day 15 and day 18 → force arrival = 15.
for i in range(n):
    s.add(If(order[i] == 1, arrivals[i] == 15, True))
# Istanbul (city index 5): Workshop between day 7 and day 11 → force arrival = 7.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 7, True))
# Barcelona (city index 6): Meet a friend between day 1 and day 5 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 1, True))

# Connectivity constraints:
# Each consecutive pair of cities in the itinerary must have a direct flight.
for i in range(n-1):
    possible_connections = []
    for (frm, to) in allowed_flights:
        possible_connections.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*possible_connections))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_idx]:10s}: [{a_day}, {d_day}]")
else:
    print("No solution found")