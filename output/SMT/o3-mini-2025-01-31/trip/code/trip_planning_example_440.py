from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 5 cities with the following properties and durations:
# 0: Split      - 2 days.
# 1: Helsinki   - 2 days.
# 2: Reykjavik  - 3 days, with a wedding event from day 10 to day 12.
#                   For a 3-day visit [S, S+2] in Reykjavik, we force S == 10.
# 3: Vilnius    - 3 days, with relatives to visit between day 7 and day 9.
#                   For a 3-day visit [S, S+2] in Vilnius, we require: S <= 9 and S+2 >= 7.
# 4: Geneva     - 6 days.
#
# Total durations = 2 + 2 + 3 + 3 + 6 = 16.
# There are 4 flights between these 5 cities (each flight overlaps one day).
# Hence, the effective trip length = 16 - 4 = 12 days.
# Thus, the departure day from the last city must be day 12.
#
# Allowed direct flights (bidirectional unless stated otherwise):
# - Split and Helsinki      : (0,1) and (1,0)
# - Geneva and Split        : (4,0) and (0,4)
# - Geneva and Helsinki     : (4,1) and (1,4)
# - Helsinki and Reykjavik  : (1,2) and (2,1)
# - Vilnius and Helsinki      : (3,1) and (1,3)
# - Split and Vilnius       : (0,3) and (3,0)

cities = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]
durations = [2, 2, 3, 3, 6]
n = len(cities)
total_trip = 12

solver = Solver()

# pos[i] represents the index of the city chosen at position i.
# They should form a permutation of {0, 1, 2, 3, 4}.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(pos[i] >= 0, pos[i] < n)

# S[i] represents the arrival (start) day for city at position i.
# Trip always starts at day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain the arrival times.
# When finishing a city (using its full duration), you take a flight that overlaps the final day.
# Thus, for each i>=1:
#     S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed flights between consecutive cities:
allowed_flights = {
    (0,1), (1,0),   # Split and Helsinki
    (4,0), (0,4),   # Geneva and Split
    (4,1), (1,4),   # Geneva and Helsinki
    (1,2), (2,1),   # Helsinki and Reykjavik
    (3,1), (1,3),   # Vilnius and Helsinki
    (0,3), (3,0)    # Split and Vilnius
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
    # For Reykjavik (city index 2): wedding days from day 10 to day 12.
    # A 3-day visit [S, S+2] must cover days 10-12; force S==10.
    solver.add(If(pos[i] == 2, S[i] == 10, True))
    
    # For Vilnius (city index 3): relatives visit between day 7 and day 9.
    # For a 3-day visit [S, S+2], require S <= 9 and S+2 >= 7.
    solver.add(If(pos[i] == 3, And(S[i] <= 9, S[i] + 2 >= 7), True))

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
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")