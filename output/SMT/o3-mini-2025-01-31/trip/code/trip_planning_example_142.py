from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 3 cities with the following properties:
# City indices and durations:
# 0: Madrid  - 4 days.
# 1: Dublin  - 3 days.
# 2: Tallinn - 2 days, with a workshop scheduled between day 6 and day 7.
# For a 2‑day visit [S, S+1] in Tallinn, to cover the workshop, we require S == 6.
#
# Total durations = 4 + 3 + 2 = 9.
# There are 2 flights (one flight between each consecutive pair),
# and each flight overlaps the last day of the previous stay.
# Hence, the effective trip length = 9 - 2 = 7 days.
# Therefore, the departure day from the last city must equal 7.

cities = ["Madrid", "Dublin", "Tallinn"]
durations = [4, 3, 2]
n = len(cities)
total_trip = 7

solver = Solver()

# Decision variables:
# pos[i] is the index of the city visited in the i-th position.
# The pos variables form a permutation of [0, 1, 2].
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] is the arrival (start) day for the city occurring at position i.
# The trip starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain the arrival times:
# When finishing the stay at city in position i-1, you take a flight that overlaps its last day.
# So S[i] = S[i-1] + (duration of city at pos[i-1] - 1), for i >= 1.
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights between consecutive cities:
# Direct flights provided: 
#   Madrid and Dublin, and Dublin and Tallinn.
# We assume flights are bidirectional.
# Map indices:
# 0: Madrid, 1: Dublin, 2: Tallinn
allowed_flights = {
    (0,1), (1,0),
    (1,2), (2,1)
}

for i in range(n-1):
    flight_options = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                flight_options.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(flight_options))

# Special event constraint for Tallinn:
# For Tallinn (city index 2), we require the arrival day S == 6.
for i in range(n):
    solver.add(If(pos[i] == 2, S[i] == 6, True))

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
        print(f" Position {i+1}: {city:8s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    
    final_day = m.evaluate(S[n-1] + durations[ itinerary[-1] ] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")