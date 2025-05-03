from z3 import *

# City indices and durations:
# 0: Oslo      (2 days)  – Friend meeting at Oslo between day 3 and 4 → force arrival = 3.
# 1: Stuttgart (3 days)
# 2: Venice    (4 days)
# 3: Split     (4 days)
# 4: Barcelona (3 days)  – Annual show in Barcelona from day 1 to 3 → force arrival = 1.
# 5: Brussels  (3 days)  – Meet a friend in Brussels between day 9 and 11 → force arrival = 9.
# 6: Copenhagen (3 days)
#
# Total raw days = 2 + 3 + 4 + 4 + 3 + 3 + 3 = 22.
# With 6 overlaps between the 7 visits, overall trip length = 22 - 6 = 16 days.

cities = ["Oslo", "Stuttgart", "Venice", "Split", "Barcelona", "Brussels", "Copenhagen"]
durations = [2, 3, 4, 4, 3, 3, 3]

# Allowed direct flights (bidirectional):
# 1. Venice and Stuttgart          (Venice <-> Stuttgart)         -> (2,1) and (1,2)
# 2. Oslo and Brussels             (Oslo <-> Brussels)            -> (0,5) and (5,0)
# 3. Split and Copenhagen          (Split <-> Copenhagen)         -> (3,6) and (6,3)
# 4. Barcelona and Copenhagen      (Barcelona <-> Copenhagen)     -> (4,6) and (6,4)
# 5. Barcelona and Venice          (Barcelona <-> Venice)         -> (4,2) and (2,4)
# 6. Brussels and Venice           (Brussels <-> Venice)          -> (5,2) and (2,5)
# 7. Barcelona and Stuttgart       (Barcelona <-> Stuttgart)      -> (4,1) and (1,4)
# 8. Copenhagen and Brussels       (Copenhagen <-> Brussels)      -> (6,5) and (5,6)
# 9. Oslo and Split                (Oslo <-> Split)               -> (0,3) and (3,0)
# 10. Oslo and Venice              (Oslo <-> Venice)              -> (0,2) and (2,0)
# 11. Barcelona and Split          (Barcelona <-> Split)          -> (4,3) and (3,4)
# 12. Oslo and Copenhagen          (Oslo <-> Copenhagen)          -> (0,6) and (6,0)
# 13. Barcelona and Oslo           (Barcelona <-> Oslo)           -> (4,0) and (0,4)
# 14. Copenhagen and Stuttgart     (Copenhagen <-> Stuttgart)     -> (6,1) and (1,6)
# 15. Split and Stuttgart          (Split <-> Stuttgart)          -> (3,1) and (1,3)
# 16. Copenhagen and Venice        (Copenhagen <-> Venice)        -> (6,2) and (2,6)
# 17. Barcelona and Brussels       (Barcelona <-> Brussels)       -> (4,5) and (5,4)

allowed_flights = []

def add_bidirectional(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Venice <-> Stuttgart
add_bidirectional(2, 1)
# 2. Oslo <-> Brussels
add_bidirectional(0, 5)
# 3. Split <-> Copenhagen
add_bidirectional(3, 6)
# 4. Barcelona <-> Copenhagen
add_bidirectional(4, 6)
# 5. Barcelona <-> Venice
add_bidirectional(4, 2)
# 6. Brussels <-> Venice
add_bidirectional(5, 2)
# 7. Barcelona <-> Stuttgart
add_bidirectional(4, 1)
# 8. Copenhagen <-> Brussels
add_bidirectional(6, 5)
# 9. Oslo <-> Split
add_bidirectional(0, 3)
# 10. Oslo <-> Venice
add_bidirectional(0, 2)
# 11. Barcelona <-> Split
add_bidirectional(4, 3)
# 12. Oslo <-> Copenhagen
add_bidirectional(0, 6)
# 13. Barcelona <-> Oslo
add_bidirectional(4, 0)
# 14. Copenhagen <-> Stuttgart
add_bidirectional(6, 1)
# 15. Split <-> Stuttgart
add_bidirectional(3, 1)
# 16. Copenhagen <-> Venice
add_bidirectional(6, 2)
# 17. Barcelona <-> Brussels
add_bidirectional(4, 5)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Model the itinerary as a permutation (order) of the 7 cities.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(order[i] >= 0, order[i] < n)
s.add(Distinct(order))

# Create arrival and departure day variables for each visit slot.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip always starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if city c is assigned then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Link consecutive visits: the arrival for visit i+1 equals the departure of visit i.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 16.
s.add(departures[n-1] == 16)

# Event-specific constraints:
# Oslo (index 0): Friend meeting must occur between day 3 and 4 → force arrival = 3.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 3, True))
# Barcelona (index 4): Annual show from day 1 to 3 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 1, True))
# Brussels (index 5): Meet friend between day 9 and 11 → force arrival = 9.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 9, True))

# Connectivity: Each consecutive pair of cities must be connected by a direct flight.
for i in range(n - 1):
    s.add(Or([And(order[i] == frm, order[i+1] == to) for (frm, to) in allowed_flights]))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        arr = m.evaluate(arrivals[i]).as_long()
        dep = m.evaluate(departures[i]).as_long()
        itinerary.append((cities[city_idx], arr, dep))
    
    print("Itinerary (City, arrival day, departure day):")
    for city, arr, dep in itinerary:
        print(f"  {city:10s}: [{arr}, {dep}]")
else:
    print("No solution found")