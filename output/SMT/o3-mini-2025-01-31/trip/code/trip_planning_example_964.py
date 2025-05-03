from z3 import *

# Cities and their durations, with event constraints:
# 0: Athens     (3 days) – Meet a friend in Athens between day 7 and day 9 ⇒ force arrival = 7.
# 1: Lyon       (5 days)
# 2: Manchester (2 days)
# 3: Prague     (3 days)
# 4: Milan      (2 days) – Conference in Milan between day 9 and day 10 ⇒ force arrival = 9.
# 5: Berlin     (4 days)
# 6: Dublin     (4 days) – Annual show in Dublin from day 1 to day 4 ⇒ force arrival = 1.
#
# Total raw days = 3 + 5 + 2 + 3 + 2 + 4 + 4 = 23.
# With 6 transitions (each subtracting one day), overall trip length = 23 - 6 = 17 days.
cities = ["Athens", "Lyon", "Manchester", "Prague", "Milan", "Berlin", "Dublin"]
durations = [3, 5, 2, 3, 2, 4, 4]

# Allowed direct flights (all bidirectional):
# 1. Dublin and Manchester      -> (Dublin, Manchester)            => (6, 2)
# 2. Athens and Milan           -> (Athens, Milan)                 => (0, 4)
# 3. Dublin and Lyon            -> (Dublin, Lyon)                  => (6, 1)
# 4. Athens and Prague          -> (Athens, Prague)                => (0, 3)
# 5. Prague and Lyon            -> (Prague, Lyon)                  => (3, 1)
# 6. Manchester and Prague      -> (Manchester, Prague)            => (2, 3)
# 7. Berlin and Milan           -> (Berlin, Milan)                 => (5, 4)
# 8. Athens and Manchester      -> (Athens, Manchester)            => (0, 2)
# 9. Dublin and Berlin          -> (Dublin, Berlin)                => (6, 5)
# 10. Dublin and Prague         -> (Dublin, Prague)                => (6, 3)
# 11. Milan and Manchester      -> (Milan, Manchester)             => (4, 2)
# 12. Berlin and Athens         -> (Berlin, Athens)                => (5, 0)
# 13. Berlin and Manchester     -> (Berlin, Manchester)            => (5, 2)
# 14. Dublin and Milan          -> (Dublin, Milan)                 => (6, 4)
# 15. Milan and Prague          -> (Milan, Prague)                 => (4, 3)
# 16. Dublin and Athens         -> (Dublin, Athens)                => (6, 0)

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# Flight 1: Dublin <-> Manchester
bidir(6, 2)
# Flight 2: Athens <-> Milan
bidir(0, 4)
# Flight 3: Dublin <-> Lyon
bidir(6, 1)
# Flight 4: Athens <-> Prague
bidir(0, 3)
# Flight 5: Prague <-> Lyon
bidir(3, 1)
# Flight 6: Manchester <-> Prague
bidir(2, 3)
# Flight 7: Berlin <-> Milan
bidir(5, 4)
# Flight 8: Athens <-> Manchester
bidir(0, 2)
# Flight 9: Dublin <-> Berlin
bidir(6, 5)
# Flight 10: Dublin <-> Prague
bidir(6, 3)
# Flight 11: Milan <-> Manchester
bidir(4, 2)
# Flight 12: Berlin <-> Athens
bidir(5, 0)
# Flight 13: Berlin <-> Manchester
bidir(5, 2)
# Flight 14: Dublin <-> Milan
bidir(6, 4)
# Flight 15: Milan <-> Prague
bidir(4, 3)
# Flight 16: Dublin <-> Athens
bidir(6, 0)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define permutation variables for the visitation order.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure times for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit, set: departure = arrival + (duration - 1)
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share one transit day.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 17.
s.add(departures[n-1] == 17)

# Event-specific constraints:
# Dublin (city index 6): Annual show from day 1 to day 4 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 1, True))
# Athens (city index 0): Meet a friend between day 7 and day 9 → force arrival = 7.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 7, True))
# Milan (city index 4): Conference between day 9 and day 10 → force arrival = 9.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 9, True))

# Connectivity constraints:
# Each consecutive pair must be connected by a direct flight.
for i in range(n-1):
    flight_possible = []
    for (frm, to) in allowed_flights:
        flight_possible.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*flight_possible))

# Solve the model and output results.
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