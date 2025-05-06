from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 6 cities with the following properties:
# City indices and durations:
# 0: Frankfurt  - 4 days, with an annual show from day 13 to day 16.
#                   For a 4-day visit [S, S+3] to cover days 13-16, we require S == 13.
# 1: Manchester - 4 days.
# 2: Valencia   - 4 days.
# 3: Naples     - 4 days.
# 4: Oslo       - 3 days.
# 5: Vilnius    - 2 days, with a wedding between day 12 and day 13.
#                   For a 2-day visit [S, S+1] to cover the wedding, we require S == 12.
#
# Total durations = 4 + 4 + 4 + 4 + 3 + 2 = 21.
# There are 5 flights connecting the 6 cities. Each flight overlaps the last day of the preceding stay,
# so the effective trip length is 21 - 5 = 16 days.
# Hence, the departure day from the final city must equal 16.

cities = ["Frankfurt", "Manchester", "Valencia", "Naples", "Oslo", "Vilnius"]
durations = [4, 4, 4, 4, 3, 2]
n = len(cities)
total_trip = 16

solver = Solver()

# Decision variables:
# pos[i] is the index of the city visited at the i-th position. They form a permutation of 0,...,5.
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

# Chain arrival times:
# After finishing a city's stay, the travel flight overlaps the last day of that stay.
# So for each consecutive city, we have:
#   S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city equals total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights:
# The cities (with indices) and allowed direct flights are:
# 0: Frankfurt, 1: Manchester, 2: Valencia, 3: Naples, 4: Oslo, 5: Vilnius
#
# Direct flights available (bidirectional unless noted otherwise):
# - Valencia and Frankfurt        -> (2,0) and (0,2)
# - Manchester and Frankfurt      -> (1,0) and (0,1)
# - Naples and Manchester         -> (3,1) and (1,3)
# - Naples and Frankfurt          -> (3,0) and (0,3)
# - Naples and Oslo               -> (3,4) and (4,3)
# - Oslo and Frankfurt            -> (4,0) and (0,4)
# - Vilnius and Frankfurt         -> (5,0) and (0,5)
# - Oslo and Vilnius              -> (4,5) and (5,4)
# - Manchester and Oslo           -> (1,4) and (4,1)
# - Valencia and Naples           -> (2,3) and (3,2)

allowed_flights = {
    (2, 0), (0, 2),
    (1, 0), (0, 1),
    (3, 1), (1, 3),
    (3, 0), (0, 3),
    (3, 4), (4, 3),
    (4, 0), (0, 4),
    (5, 0), (0, 5),
    (4, 5), (5, 4),
    (1, 4), (4, 1),
    (2, 3), (3, 2)
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
    # For Frankfurt (city index 0) the show from day 13 to day 16 forces the start day to be 13.
    solver.add(If(pos[i] == 0, S[i] == 13, True))
    # For Vilnius (city index 5) the wedding between day 12 and day 13 forces the start day to be 12.
    solver.add(If(pos[i] == 5, S[i] == 12, True))

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