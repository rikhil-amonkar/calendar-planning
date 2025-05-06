from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 6 cities with the following properties:
# 0: Reykjavik - 5 days, no special event.
# 1: Istanbul  - 4 days, with a friend meeting event that must occur
#                  between day 5 and day 8. For its 4-day stay [S, S+3],
#                  require S <= 8 and S+3 >= 5.
# 2: Edinburgh - 5 days, no special event.
# 3: Oslo      - 2 days, with a relatives visit event that must occur
#                  between day 8 and day 9. For its 2-day stay [S, S+1],
#                  require S <= 9 and S+1 >= 8.
# 4: Stuttgart - 3 days, no special event.
# 5: Bucharest - 5 days, no special event.
#
# Total durations = 5 + 4 + 5 + 2 + 3 + 5 = 24.
# There are 5 flights between the 6 cities, each flight overlapping one day.
# Effective trip length = 24 - 5 = 19 days.
# Thus, the departure day from the final city must equal 19.
#
# Allowed direct flights between cities:
# - Bucharest and Oslo        : (5,3) and (3,5)
# - Istanbul and Oslo         : (1,3) and (3,1)
# - from Reykjavik to Stuttgart: (0,4) only (unidirectional)
# - Bucharest and Istanbul    : (5,1) and (1,5)
# - Stuttgart and Edinburgh   : (4,2) and (2,4)
# - Istanbul and Edinburgh    : (1,2) and (2,1)
# - Oslo and Reykjavik        : (3,0) and (0,3)
# - Istanbul and Stuttgart    : (1,4) and (4,1)
# - Oslo and Edinburgh        : (3,2) and (2,3)

cities    = ["Reykjavik", "Istanbul", "Edinburgh", "Oslo", "Stuttgart", "Bucharest"]
durations = [5,            4,          5,          2,     3,           5]
n = len(cities)
total_trip = 19

solver = Solver()

# pos[i] will be the index of the city visited at position i in the trip.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(pos[i] >= 0, pos[i] < n)

# S[i] is the arrival (start) day for the city at position i.
# The trip begins on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain the start days based on durations and flight overlaps:
# After finishing city at position i-1 (spending its duration),
# because a flight overlaps the last day, the next city's arrival is:
#   S[i] = S[i-1] + (duration(city_at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The last city's departure day must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed flights constraints for consecutive cities:
allowed_flights = {
    (5,3), (3,5),    # Bucharest <-> Oslo
    (1,3), (3,1),    # Istanbul <-> Oslo
    (0,4),           # Reykjavik -> Stuttgart (unidirectional)
    (5,1), (1,5),    # Bucharest <-> Istanbul
    (4,2), (2,4),    # Stuttgart <-> Edinburgh
    (1,2), (2,1),    # Istanbul <-> Edinburgh
    (3,0), (0,3),    # Oslo <-> Reykjavik
    (1,4), (4,1),    # Istanbul <-> Stuttgart
    (3,2), (2,3)     # Oslo <-> Edinburgh
}

for i in range(n - 1):
    opts = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                opts.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(opts))

# Special event constraints:
for i in range(n):
    # Istanbul event: friend meeting between day 5 and day 8.
    # For a 4-day stay [S, S+3] at Istanbul (city index 1):
    solver.add(If(pos[i] == 1, And(S[i] <= 8, S[i] + 3 >= 5), True))
    
    # Oslo event: relatives visit between day 8 and day 9.
    # For a 2-day stay [S, S+1] at Oslo (city index 3):
    solver.add(If(pos[i] == 3, And(S[i] <= 9, S[i] + 1 >= 8), True))

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
        departure = arrival + durations[itinerary[i]] - 1
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")