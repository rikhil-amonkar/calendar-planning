from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 8 cities with the following properties:
# 0: Reykjavik  - 2 days, with a friend meeting event between day 3 and day 4.
#                   For its 2-day visit (days S .. S+1), we require S <= 4 and S+1 >= 3.
# 1: Stockholm  - 2 days, with a friends tour event between day 4 and day 5.
#                   For its 2-day visit (days S .. S+1), we require S <= 5 and S+1 >= 4.
# 2: Porto      - 5 days, with a wedding event between day 13 and day 17.
#                   For its 5-day visit (days S .. S+4), we require S <= 17 and S+4 >= 13.
# 3: Nice       - 3 days.
# 4: Venice     - 4 days.
# 5: Vienna     - 3 days, with a workshop event between day 11 and day 13.
#                   For its 3-day visit (days S .. S+2), we require S <= 13 and S+2 >= 11.
# 6: Split      - 3 days.
# 7: Copenhagen - 2 days.
#
# Total durations = 2+2+5+3+4+3+3+2 = 24.
# We have 8 cities, so 7 flights between visits. Each flight overlaps one day.
# Effective trip length = 24 - 7 = 17 days.
# The final departure day (arrival at last city + its duration - 1) must equal 17.

# Allowed direct flights (bidirectional):
#  - Copenhagen and Vienna       : (7,5) and (5,7)
#  - Nice and Stockholm           : (3,1) and (1,3)
#  - Split and Copenhagen         : (6,7) and (7,6)
#  - Nice and Reykjavik           : (3,0) and (0,3)
#  - Nice and Porto               : (3,2) and (2,3)
#  - Reykjavik and Vienna         : (0,5) and (5,0)
#  - Stockholm and Copenhagen     : (1,7) and (7,1)
#  - Nice and Venice              : (3,4) and (4,3)
#  - Nice and Vienna              : (3,5) and (5,3)
#  - Reykjavik and Copenhagen     : (0,7) and (7,0)
#  - Nice and Copenhagen          : (3,7) and (7,3)
#  - Stockholm and Vienna         : (1,5) and (5,1)
#  - Venice and Vienna            : (4,5) and (5,4)
#  - Copenhagen and Porto         : (7,2) and (2,7)
#  - Reykjavik and Stockholm      : (0,1) and (1,0)
#  - Stockholm and Split          : (1,6) and (6,1)
#  - Split and Vienna             : (6,5) and (5,6)
#  - Copenhagen and Venice        : (7,4) and (4,7)
#  - Vienna and Porto             : (5,2) and (2,5)

cities     = ["Reykjavik", "Stockholm", "Porto", "Nice", "Venice", "Vienna", "Split", "Copenhagen"]
durations  = [2,            2,           5,      3,      4,       3,       3,       2]
n          = len(cities)
total_trip = 17

solver = Solver()

# Decision variables:
# pos[i] is the index of the city visited in the i-th position of the itinerary.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] is the arrival day at the city in position i.
# The trip begins on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain the arrival days such that when leaving the city at position i-1,
# the next city is entered the same day as the flight "overlap".
# For i >= 1, S[i] = S[i-1] + (duration(city at pos[i-1]) - 1).
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# Final departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed flights constraints between consecutive cities:
allowed_flights = {
    (7,5), (5,7),         # Copenhagen <-> Vienna
    (3,1), (1,3),         # Nice <-> Stockholm
    (6,7), (7,6),         # Split <-> Copenhagen
    (3,0), (0,3),         # Nice <-> Reykjavik
    (3,2), (2,3),         # Nice <-> Porto
    (0,5), (5,0),         # Reykjavik <-> Vienna
    (1,7), (7,1),         # Stockholm <-> Copenhagen
    (3,4), (4,3),         # Nice <-> Venice
    (3,5), (5,3),         # Nice <-> Vienna
    (0,7), (7,0),         # Reykjavik <-> Copenhagen
    (3,7), (7,3),         # Nice <-> Copenhagen
    (1,5), (5,1),         # Stockholm <-> Vienna
    (4,5), (5,4),         # Venice <-> Vienna
    (7,2), (2,7),         # Copenhagen <-> Porto
    (0,1), (1,0),         # Reykjavik <-> Stockholm
    (1,6), (6,1),         # Stockholm <-> Split
    (6,5), (5,6),         # Split <-> Vienna
    (7,4), (4,7),         # Copenhagen <-> Venice
    (5,2), (2,5)          # Vienna <-> Porto
}

for i in range(n - 1):
    flight_options = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                flight_options.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(flight_options))

# Special event constraints:
for i in range(n):
    # Reykjavik (index 0): friend meeting between day 3 and day 4.
    solver.add(If(pos[i] == 0, And(S[i] <= 4, S[i] + 1 >= 3), True))
    
    # Stockholm (index 1): tour with friends between day 4 and day 5.
    solver.add(If(pos[i] == 1, And(S[i] <= 5, S[i] + 1 >= 4), True))
    
    # Porto (index 2): wedding event between day 13 and day 17.
    solver.add(If(pos[i] == 2, And(S[i] <= 17, S[i] + 4 >= 13), True))
    
    # Vienna (index 5): workshop event between day 11 and day 13.
    solver.add(If(pos[i] == 5, And(S[i] <= 13, S[i] + 2 >= 11), True))

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
        print(f" Position {i+1}: {city:12s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")