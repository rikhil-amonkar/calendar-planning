from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# City indices and properties:
# 0: Salzburg   - 4 days.
# 1: Stockholm  - 2 days.
# 2: Venice     - 5 days, with an annual show from day 1 to day 5.
#                To attend the show, the 5-day visit [S, S+4] must cover days 1–5,
#                hence we force the arrival day of Venice to be S == 1.
# 3: Frankfurt  - 4 days.
# 4: Florence   - 4 days.
# 5: Barcelona  - 2 days.
# 6: Stuttgart  - 3 days.
#
# Total durations = 4 + 2 + 5 + 4 + 4 + 2 + 3 = 24.
# There are 6 flights (each flight overlaps one day), so effective trip length = 24 − 6 = 18 days.
# Thus, the departure day from the last city must equal 18.

cities = ["Salzburg", "Stockholm", "Venice", "Frankfurt", "Florence", "Barcelona", "Stuttgart"]
durations = [4, 2, 5, 4, 4, 2, 3]
n = len(cities)
total_trip = 18

solver = Solver()

# pos[i] is the index of the city visited at position i;
# the pos vector must be a permutation of indices 0..6.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] is the arrival (start) day of the city at position i.
# The trip starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain the arrival times considering that each flight overlaps the last day of a city's stay.
# For i>=1: S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights between consecutive cities.
# City indices: 0=Salzburg, 1=Stockholm, 2=Venice, 3=Frankfurt, 4=Florence, 5=Barcelona, 6=Stuttgart.
# Allowed flights (bidirectional):
# - Barcelona and Frankfurt:         (5,3) and (3,5)
# - Florence and Frankfurt:          (4,3) and (3,4)
# - Stockholm and Barcelona:         (1,5) and (5,1)
# - Barcelona and Florence:          (5,4) and (4,5)
# - Venice and Barcelona:            (2,5) and (5,2)
# - Stuttgart and Barcelona:         (6,5) and (5,6)
# - Frankfurt and Salzburg:          (3,0) and (0,3)
# - Stockholm and Frankfurt:         (1,3) and (3,1)
# - Stuttgart and Stockholm:         (6,1) and (1,6)
# - Stuttgart and Frankfurt:         (6,3) and (3,6)
# - Venice and Stuttgart:            (2,6) and (6,2)
# - Venice and Frankfurt:            (2,3) and (3,2)
allowed_flights = {
    (5,3), (3,5),
    (4,3), (3,4),
    (1,5), (5,1),
    (5,4), (4,5),
    (2,5), (5,2),
    (6,5), (5,6),
    (3,0), (0,3),
    (1,3), (3,1),
    (6,1), (1,6),
    (6,3), (3,6),
    (2,6), (6,2),
    (2,3), (3,2)
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
    # For Venice (city index 2): the annual show is from day 1 to day 5.
    # A 5-day visit [S, S+4] must cover these days, so force S == 1.
    solver.add(If(pos[i] == 2, S[i] == 1, True))

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
    
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")