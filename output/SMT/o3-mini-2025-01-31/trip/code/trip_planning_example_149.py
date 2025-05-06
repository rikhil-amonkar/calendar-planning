from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 3 cities with the following properties:
# 0: London     - 3 days, no special event.
# 1: Santorini  - 6 days, with a conference: the 6-day visit [S, S+5] must include day 5 and day 10.
#                That is, we require S <= 5 and S + 5 >= 10.
# 2: Istanbul   - 3 days, no special event.
#
# Total durations = 3 + 6 + 3 = 12 days.
# There will be 2 flights between the 3 cities (each flight overlaps one day),
# so the effective trip length is 12 - 2 = 10 days.
# The final departure day must equal 10.

# Allowed direct flights (bidirectional):
#   Istanbul <-> London, and London <-> Santorini.
#
# This means the allowed pairs (by city index) are:
#   (2, 0) and (0, 2)   [Istanbul <-> London]
#   (0, 1) and (1, 0)   [London <-> Santorini]
#
# Note that there is no direct flight between Istanbul and Santorini.
# Thus, the only valid itineraries are those where London is between Istanbul and Santorini.
#
# For instance, one valid itinerary is: Istanbul -> London -> Santorini.
# (The reverse itinerary Santorini -> London -> Istanbul would not work
#  for the conference event in Santorini, as its visit would start too early.)

cities = ["London", "Santorini", "Istanbul"]
durations = [3, 6, 3]
n = len(cities)
total_trip = 10

solver = Solver()

# Decision variables:
# pos[i] is the index of the city visited in position i.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] is the arrival day (start day) for the city in position i.
# The trip starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Link the arrival days:
# When finishing the visit of the city at position i-1,
# the next city is entered on the same day as the flight "overlap".
# For i>=1, we have:
#    S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The final departure day equals the trip total.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed flights between consecutive cities:
allowed_flights = {
    (2, 0), (0, 2),   # Istanbul <-> London
    (0, 1), (1, 0)    # London <-> Santorini
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
    # Santorini (index 1) conference: for its 6-day visit [S, S+5], days 5 and 10 must fall within.
    solver.add(If(pos[i] == 1, And(S[i] <= 5, S[i] + 5 >= 10), True))

# -----------------------------------------------------------------------------
# Solve the model.
# -----------------------------------------------------------------------------
if solver.check() == sat:
    m = solver.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals  = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        idx = itinerary[i]
        city = cities[idx]
        arrival = arrivals[i]
        departure = arrival + durations[idx] - 1
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")