from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 4 cities with the following properties:
# Let's assign indices:
# 0: Split      - 5 days.
# 1: Vilnius    - 4 days.
# 2: Santorini  - 2 days, with a conference that must occur during days 13 and 14.
#                   For its 2‑day visit [S, S+1], this forces S == 13.
# 3: Madrid     - 6 days.
#
# Total durations = 5 + 4 + 2 + 6 = 17.
# There are 3 flights between the 4 cities (each flight overlaps one day).
# Effective trip length = 17 − 3 = 14 days. Hence, the departure day from the last city must be 14.
#
# Allowed direct flights (bidirectional unless otherwise noted) are:
# - Vilnius and Split      : allowed pairs (1,0) and (0,1)
# - Split and Madrid       : allowed pairs (0,3) and (3,0)
# - Madrid and Santorini   : allowed pairs (3,2) and (2,3)
#
# In this flight network the only possible chain that connects all 4 cities is:
#     Vilnius --> Split --> Madrid --> Santorini
#
# Notice: The reverse chain Santorini --> Madrid --> Split --> Vilnius
# would force Santorini on day 1, violating its conference constraint.
#
# We now formulate the problem using the Z3 solver.

n = 4
total_trip = 14
cities = ["Split", "Vilnius", "Santorini", "Madrid"]
durations = [5, 4, 2, 6]

solver = Solver()

# pos[i] represents the city visited at the i-th stop, i=0,...,3.
# They must form a permutation of {0,1,2,3}.
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

# Chain the arrival times.
# When you finish a city (spending its full duration) you take a direct flight that overlaps the final day.
# Hence, for each i >= 1: 
#    S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights between consecutive cities:
# Allowed flights (as ordered pairs) are:
#   - Vilnius and Split      : (1,0) and (0,1)
#   - Split and Madrid       : (0,3) and (3,0)
#   - Madrid and Santorini   : (3,2) and (2,3)
allowed_flights = {
    (1,0), (0,1),
    (0,3), (3,0),
    (3,2), (2,3)
}

for i in range(n-1):
    flight_conditions = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                flight_conditions.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(flight_conditions))

# Special event constraint:
# Santorini (city index 2) must be visited with its 2-day stay covering days 13 and 14.
# This forces the arrival day for Santorini to be day 13.
for i in range(n):
    solver.add(If(pos[i] == 2, S[i] == 13, True))

# -----------------------------------------------------------------------------
# Solve the model.
# -----------------------------------------------------------------------------
if solver.check() == sat:
    m = solver.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    schedule  = [m.evaluate(S[i]).as_long() for i in range(n)]

    print("Trip Itinerary:")
    for i in range(n):
        city_index = itinerary[i]
        city_name = cities[city_index]
        arrival = schedule[i]
        departure = arrival + durations[city_index] - 1
        print(f" Position {i+1}: {city_name:11s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")