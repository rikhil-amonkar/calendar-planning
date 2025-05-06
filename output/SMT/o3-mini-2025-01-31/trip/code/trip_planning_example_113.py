from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 3 cities with the following properties:
# Let's assign indices as follows:
# 0: Naples    - 3 days.
# 1: Seville   - 4 days, with an annual show from day 9 to day 12.
#                This forces the visit's start day to be 9 so that the show is fully attended.
# 2: Milan     - 7 days.
#
# Total durations = 3 + 4 + 7 = 14.
# There are 2 flights between 3 cities (each flight overlaps one day).
# Hence the effective trip length = 14 - 2 = 12 days.
# So the departure day from the last city must be day 12.
#
# Allowed direct flights are:
# - "Naples and Milan"       : bidirectional; allowed pairs: (0,2) and (2,0).
# - "Milan and Seville"      : bidirectional; allowed pairs: (2,1) and (1,2).
#
# Thus the only valid order is:
#     Naples  -> Milan  -> Seville
#
# and the schedule would be computed as follows:
#   S[0] = 1  (Naples arrives on day 1)
#   S[1] = S[0] + (3 - 1) = 1 + 2 = 3  (Milan arrives on day 3)
#   S[2] = S[1] + (7 - 1) = 3 + 6 = 9  (Seville arrives on day 9)
#   Departure from Seville = 9 + (4 - 1) = 12
#
# This satisfies the annual show constraint in Seville (covering days 9–12).

cities = ["Naples", "Seville", "Milan"]
durations = [3, 4, 7]
n = len(cities)
total_trip = 12

solver = Solver()

# pos[i] represents the index of the city visited in the i-th position.
# They must be a permutation of {0, 1, 2}.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] is the arrival (start) day for the city at position i.
# The trip always starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Time chaining:
# When you finish a city's stay, you take a direct flight that overlaps the final day.
# That is, for each consecutive city:
#    S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights constraints for consecutive cities:
# Allowed flights (as ordered pairs) are:
# - Naples and Milan: (0,2) and (2,0)
# - Milan and Seville: (2,1) and (1,2)
allowed_flights = {
    (0,2), (2,0),
    (2,1), (1,2)
}

for i in range(n - 1):
    flight_options = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                flight_options.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(flight_options))

# Special event constraint:
# For Seville (city index 1): the annual show is from day 9 to day 12.
# Since Seville has a 4-day stay [S, S+3], to cover days 9–12 we force S == 9.
for i in range(n):
    solver.add(If(pos[i] == 1, S[i] == 9, True))

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
        city = cities[city_index]
        arrival = schedule[i]
        departure = arrival + durations[city_index] - 1
        print(f" Position {i+1}: {city:9s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")