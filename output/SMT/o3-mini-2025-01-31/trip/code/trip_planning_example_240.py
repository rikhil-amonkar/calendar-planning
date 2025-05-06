from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 4 cities:
# 0: Prague    - 2 days, no extra event constraint.
# 1: Berlin    - 3 days, and you must attend a conference there on day 6 and day 8.
#                For a 3-day visit [S, S+2] to cover days 6 and 8, we require S == 6.
# 2: Tallinn   - 5 days, and you plan to visit relatives in Tallinn between day 8 and day 12.
#                For a 5-day visit [S, S+4] to overlap [8,12], a sufficient condition is:
#                   S <= 12 and S+4 >= 8.
# 3: Stockholm - 5 days, no extra event constraint.
#
# Total planned trip days, computed with overlap of flights, is:
# Sum(durations) - (# flights) = (2 + 3 + 5 + 5) - 3 = 15 - 3 = 12.
# So the trip ends on day 12.
#
# Allowed direct flights (bidirectional unless specified otherwise):
# - Berlin and Tallinn:      (1,2) and (2,1)
# - Prague and Tallinn:      (0,2) and (2,0)
# - Stockholm and Tallinn:   (3,2) and (2,3)
# - Prague and Stockholm:    (0,3) and (3,0)
# - Stockholm and Berlin:    (3,1) and (1,3)

cities = ["Prague", "Berlin", "Tallinn", "Stockholm"]
durations = [2, 3, 5, 5]
n = len(cities)
total_trip = 12

solver = Solver()

# Decision variables:
# pos[i] is the index of the city visited at position i (all distinct).
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] is the arrival day for the city in position i.
# The trip always starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Compute arrival times in a chained manner.
# When moving from one city to the next, we "overlap" the flight day.
# So for i >= 1, S[i] = S[i-1] + (duration(previous city) - 1).
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# Final trip day constraint: Departure day from the last city equals total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed flights constraints between consecutive cities.
allowed_flights = {
    (1,2), (2,1),  # Berlin <-> Tallinn
    (0,2), (2,0),  # Prague <-> Tallinn
    (3,2), (2,3),  # Stockholm <-> Tallinn
    (0,3), (3,0),  # Prague <-> Stockholm
    (3,1), (1,3)   # Stockholm <-> Berlin
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
    # For Berlin (index 1): Conference on day 6 and day 8 requires a 3-day visit to cover both,
    # which happens only if the visit starts on day 6 (covers days 6,7,8).
    solver.add(If(pos[i] == 1, S[i] == 6, True))
    
    # For Tallinn (index 2): The 5-day visit (days S ... S+4) must overlap the interval [8,12].
    # Sufficient constraints: S[i] <= 12 and S[i] + 4 >= 8.
    solver.add(If(pos[i] == 2, And(S[i] <= 12, S[i] + 4 >= 8), True))
    
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
        city_name = cities[city_index]
        arrival = arrivals[i]
        departure = arrival + durations[city_index] - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")