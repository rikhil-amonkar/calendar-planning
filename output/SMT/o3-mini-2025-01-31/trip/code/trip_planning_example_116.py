from z3 import Solver, Int, IntVector, And, If, sat

# In our problem we have 3 cities with fixed durations and an event in Santorini:
#
#   • Split: 6 days
#   • Santorini: 7 days; during its stay you must attend a conference on day 12 and day 18.
#   • London: 7 days
#
# The effective trip length, if we “save” one day in every flight connection, is:
#     total = (6) + (7 – 1) + (7 – 1) = 6 + 6 + 6 = 18.
#
# The allowed direct flights are:
#   – London ↔ Santorini
#   – Split ↔ London
#
# Since there is no direct flight between Split and Santorini, the only possible itinerary is:
#
#     Position 1: Split   (6 days)
#     Position 2: London  (7 days)
#     Position 3: Santorini (7 days)
#
# We also need the conference in Santorini to be attended during day 12 and day 18.
# When Santorini is visited last, its days will be exactly from its arrival day A to A+6.
# To cover both day 12 and day 18 we must have A <= 12 and A+6 >= 18.
# In fact, the only possibility is A = 12 so that the Santorini interval is [12, 18].
#
# We label our cities as follows:
#
#   0 : Split    (6 days)
#   1 : Santorini  (7 days)  -- Must start on day 12 so that its interval is [12,18]
#   2 : London     (7 days)
#
# We now set up a simple Z3 model.
#
# In our model, we represent the itinerary as an ordering of the 3 cities.
# For simplicity, we already know the required order:
#    pos[0] = Split, pos[1] = London, pos[2] = Santorini.
#
# We then assign an “arrival day” S[i] for the city in position i.
#
# We use the following recurrence (with instantaneous flights and “saving” an overlap day):
#
#    S[0] = 1.
#    For i >= 1, S[i] = S[i-1] + (duration(city at position i-1) – 1).
#
# Finally, the trip must exactly end on day 18:
#
#    S[2] + (duration(city at pos[2]) – 1) = 18.
# For our durations, that becomes: S[2] + 6 = 18  →  S[2] = 12.
#
# The allowed flight constraints are verified on each adjacent pair:
#   • From Split (0) to London (2): allowed (Split and London).
#   • From London (2) to Santorini (1): allowed (London and Santorini).
#
# Event constraint:
#   For Santorini (city index 1), we require that its arrival day S is 12.
#
# We now implement the Z3 model.

cities = ["Split", "Santorini", "London"]
durations = [6, 7, 7]   # corresponding durations

n = 3
total_trip = 18

solver = Solver()

# Decision variables:
# Let pos[i] be the city visited in the i-th position.
# We know the required order; we force:
#   pos[0] = 0 (Split), pos[1] = 2 (London), pos[2] = 1 (Santorini)
pos = [Int(f"pos_{i}") for i in range(n)]
solver.add(pos[0] == 0)
solver.add(pos[1] == 2)
solver.add(pos[2] == 1)

# Arrival time variables: S[i] is the arrival day for city in position i.
S = [Int(f"S_{i}") for i in range(n)]
solver.add(S[0] == 1)  # Trip starts on day 1

# Recurrence for arrival days (using the “overlap” of one day on each transition):
# For i >= 1: S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    # When pos[i-1] equals a constant, we pick the corresponding duration.
    duration_prev = If(pos[i-1] == 0, durations[0],
                   If(pos[i-1] == 1, durations[1],
                   durations[2]))
    solver.add(S[i] == S[i-1] + (duration_prev - 1))

# Final departure constraint:
# The trip ends when the last city’s visit is completed.
# That is: S[2] + (duration(city at pos[2]) - 1) == total_trip.
duration_last = If(pos[n-1] == 0, durations[0],
                If(pos[n-1] == 1, durations[1],
                durations[2]))
solver.add(S[n-1] + (duration_last - 1) == total_trip)

# Allowed flights constraints: For consecutive cities.
# Allowed flights (bidirectional) are:
#   - London ↔ Santorini  (i.e., (2,1) and (1,2))
#   - Split   ↔ London     (i.e., (0,2) and (2,0))
#
# Since our permutation is fixed, we check:
#   From pos[0] to pos[1]:
#     (pos[0], pos[1]) must be either (0,2) or (2,0).
#   From pos[1] to pos[2]:
#     (pos[1], pos[2]) must be either (2,1) or (1,2).
solver.add(Or(And(pos[0] == 0, pos[1] == 2),
              And(pos[0] == 2, pos[1] == 0)))
solver.add(Or(And(pos[1] == 2, pos[2] == 1),
              And(pos[1] == 1, pos[2] == 2)))

# Event constraint:
# For Santorini (city index 1), the conference must be attended on day 12 and day 18.
# Because the visit lasts 7 days, to cover both day 12 and day 18 the only possibility (with contiguous days)
# is that Santorini is scheduled from day 12 to day 18.
# Our model then requires that whenever pos[i] == 1, its arrival S[i] must be 12.
for i in range(n):
    solver.add(If(pos[i] == 1, S[i] == 12, True))

# -----------------------------------------------------------------------------
# Solve the model.
# -----------------------------------------------------------------------------
if solver.check() == sat:
    m = solver.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals  = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city = cities[itinerary[i]]
        arrival = arrivals[i]
        depart = arrival + durations[itinerary[i]] - 1
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrival:2d} | Departure: Day {depart:2d}")
    print("Trip ends on Day:", m.evaluate(S[n-1] + durations[itinerary[-1]] - 1))
else:
    print("No valid trip plan could be found.")