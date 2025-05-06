from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 10 cities with the following properties:
# City indices and durations:
# 0: Prague     - 5 days.
# 1: Tallinn    - 3 days, with a relatives visit between day 18 and day 20.
#                For a 3‑day visit [S, S+2] we require: S <= 20 and S+2 >= 18.
# 2: Warsaw     - 2 days.
# 3: Porto      - 3 days.
# 4: Naples     - 5 days.
# 5: Milan      - 3 days, with a friend meeting between day 24 and day 26.
#                For a 3‑day visit [S, S+2] we require: S <= 26 and S+2 >= 24.
# 6: Lisbon     - 5 days.
# 7: Santorini  - 5 days.
# 8: Riga       - 4 days, with an annual show from day 5 to day 8.
#                For a 4‑day visit [S, S+3] we require S == 5.
# 9: Stockholm - 2 days.
#
# Total durations = 5+3+2+3+5+3+5+5+4+2 = 37.
# There are 9 flights (one flight between each consecutive pair),
# and each flight overlaps one day, so effective trip length = 37 - 9 = 28 days.
# Therefore, the departure day from the last city must equal 28.

cities = ["Prague", "Tallinn", "Warsaw", "Porto", "Naples", "Milan", "Lisbon", "Santorini", "Riga", "Stockholm"]
durations = [5, 3, 2, 3, 5, 3, 5, 5, 4, 2]
n = len(cities)
total_trip = 28

solver = Solver()

# Decision variables:
# pos[i] represents the index of the city visited in the i-th position.
# They form a permutation of {0,1,...,9}.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] represents the arrival (start) day for the city at position i.
# The trip starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain the arrival times:
# When finishing a city's stay, you take a flight that overlaps its final day.
# So for each consecutive city:
#   S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city must be total_trip
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights (each flight is allowed between consecutive cities):
# City indices:
# 0: Prague
# 1: Tallinn
# 2: Warsaw
# 3: Porto
# 4: Naples
# 5: Milan
# 6: Lisbon
# 7: Santorini
# 8: Riga
# 9: Stockholm

# Allowed flights (bidirectional unless specified as one-way):
allowed_flights = {
    # Riga and Prague
    (8,0), (0,8),
    # Stockholm and Milan
    (9,5), (5,9),
    # Riga and Milan
    (8,5), (5,8),
    # Lisbon and Stockholm
    (6,9), (9,6),
    # from Stockholm to Santorini (one-way)
    (9,7),
    # Naples and Warsaw
    (4,2), (2,4),
    # Lisbon and Warsaw
    (6,2), (2,6),
    # Naples and Milan
    (4,5), (5,4),
    # Lisbon and Naples
    (6,4), (4,6),
    # from Riga to Tallinn (one-way)
    (8,1),
    # Tallinn and Prague
    (1,0), (0,1),
    # Stockholm and Warsaw
    (9,2), (2,9),
    # Riga and Warsaw
    (8,2), (2,8),
    # Lisbon and Riga
    (6,8), (8,6),
    # Riga and Stockholm
    (8,9), (9,8),
    # Lisbon and Porto
    (6,3), (3,6),
    # Lisbon and Prague
    (6,0), (0,6),
    # Milan and Porto
    (5,3), (3,5),
    # Prague and Milan
    (0,5), (5,0),
    # Lisbon and Milan
    (6,5), (5,6),
    # Warsaw and Porto
    (2,3), (3,2),
    # Warsaw and Tallinn
    (2,1), (1,2),
    # Santorini and Milan
    (7,5), (5,7),
    # Stockholm and Prague
    (9,0), (0,9),
    # Stockholm and Tallinn
    (9,1), (1,9),
    # Warsaw and Milan
    (2,5), (5,2),
    # Santorini and Naples
    (7,4), (4,7),
    # Warsaw and Prague
    (2,0), (0,2)
}

for i in range(n-1):
    flight_options = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                flight_options.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(flight_options))

# Special event constraints:
for i in range(n):
    # For Tallinn (city index 1): relatives visit between day 18 and day 20
    # 3-day visit [S, S+2]: require S <= 20 and S+2 >= 18.
    solver.add(If(pos[i] == 1, And(S[i] <= 20, S[i] + 2 >= 18), True))
    
    # For Milan (city index 5): friend meeting between day 24 and day 26
    # 3-day visit [S, S+2]: require S <= 26 and S[i] + 2 >= 24.
    solver.add(If(pos[i] == 5, And(S[i] <= 26, S[i] + 2 >= 24), True))
    
    # For Riga (city index 8): annual show from day 5 to day 8; force S == 5.
    solver.add(If(pos[i] == 8, S[i] == 5, True))

# -----------------------------------------------------------------------------
# Solve the model.
# -----------------------------------------------------------------------------
if solver.check() == sat:
    m = solver.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals  = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city_index = itinerary[i]
        city = cities[city_index]
        arrival = arrivals[i]
        departure = arrival + durations[city_index] - 1
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    
    final_day = m.evaluate(S[n-1] + durations[ itinerary[-1] ] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")