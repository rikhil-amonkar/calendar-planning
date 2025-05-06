from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 6 cities with the following properties:
# 0: Porto      - 5 days.
# 1: Prague     - 4 days.
# 2: Reykjavik  - 4 days, and you must attend a wedding there between day 4 and day 7.
#                   For a 4‐day visit [S, S+3] to cover the wedding window, we require S == 4.
# 3: Santorini  - 2 days.
# 4: Amsterdam  - 2 days, and you must attend a conference there on day 14 and day 15.
#                   For a 2‐day visit [S, S+1] to cover day 14 and 15, we require S == 14.
# 5: Munich     - 4 days, and you want to meet a friend in Munich between day 7 and day 10.
#                   For a 4‐day visit [S, S+3] to intersect [7,10] we require S <= 10 and S+3 >= 7.
#
# The total visit durations sum = (5 + 4 + 4 + 2 + 2 + 4) = 21.
# When traveling by direct flights (one flight per connection between cities), we subtract (6 - 1) = 5 days
# so the trip ends on day 21 - 5 = 16.
# Total trip length = 16 days.
#
# Allowed direct flights (bidirectional unless stated otherwise):
# - Porto and Amsterdam:        (0,4) and (4,0)
# - Munich and Amsterdam:       (5,4) and (4,5)
# - Reykjavik and Amsterdam:    (2,4) and (4,2)
# - Munich and Porto:           (5,0) and (0,5)
# - Prague and Reykjavik:       (1,2) and (2,1)
# - Reykjavik and Munich:       (2,5) and (5,2)
# - Amsterdam and Santorini:    (4,3) and (3,4)
# - Prague and Amsterdam:       (1,4) and (4,1)
# - Prague and Munich:          (1,5) and (5,1)

cities = ["Porto", "Prague", "Reykjavik", "Santorini", "Amsterdam", "Munich"]
durations = [5, 4, 4, 2, 2, 4]
n = len(cities)
total_trip = 16

solver = Solver()

# Decision variables:
# pos[i] is the index of the city visited at the i-th position.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] is the arrival day at the city in position i.
# The trip starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Transit: When moving consecutively from one city to the next,
# the arrival day S[i] = S[i-1] + (duration(previous city) - 1).
for i in range(1, n):
    expr = Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)])
    solver.add(S[i] == S[i-1] + expr)

# Final departure day constraint:
# Departure day from the last city is S[n-1] + (duration(last city) - 1) == total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights constraints between consecutive cities:
allowed_flights = {
    (0,4), (4,0),     # Porto <-> Amsterdam
    (5,4), (4,5),     # Munich <-> Amsterdam
    (2,4), (4,2),     # Reykjavik <-> Amsterdam
    (5,0), (0,5),     # Munich <-> Porto
    (1,2), (2,1),     # Prague <-> Reykjavik
    (2,5), (5,2),     # Reykjavik <-> Munich
    (4,3), (3,4),     # Amsterdam <-> Santorini
    (1,4), (4,1),     # Prague <-> Amsterdam
    (1,5), (5,1)      # Prague <-> Munich
}
for i in range(n - 1):
    options = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                options.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(options))

# Special event constraints:
for i in range(n):
    # For Reykjavik (index 2): Wedding between day 4 and 7.
    # With a 4-day visit (days S...S+3), force start day S to be 4.
    solver.add(If(pos[i] == 2, S[i] == 4, True))
    
    # For Amsterdam (index 4): Conference on day 14 and day 15.
    # With a 2-day visit (days S, S+1), force S == 14.
    solver.add(If(pos[i] == 4, S[i] == 14, True))
    
    # For Munich (index 5): Meeting a friend between day 7 and day 10.
    # With a 4-day visit (days S...S+3), ensure the visit overlaps the interval [7,10]:
    # This is satisfied if S <= 10 and S+3 >= 7.
    solver.add(If(pos[i] == 5, And(S[i] <= 10, S[i] + 3 >= 7), True))

# -----------------------------------------------------------------------------
# Solve the model.
# -----------------------------------------------------------------------------
if solver.check() == sat:
    m = solver.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals  = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city_idx = itinerary[i]
        city = cities[city_idx]
        arrival = arrivals[i]
        departure = arrival + durations[city_idx] - 1
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")