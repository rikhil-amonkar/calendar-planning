from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 6 cities with the following properties:
# City indices and durations:
# 0: Helsinki   - 4 days.
# 1: Valencia   - 5 days.
# 2: Dubrovnik  - 4 days.
# 3: Porto      - 3 days, with a friend meeting between day 16 and day 18.
#                A 3‑day visit spans days [S, S+2], so we require that:
#                  S <= 18    and    S + 2 >= 16
# 4: Prague     - 3 days.
# 5: Reykjavik  - 4 days.
#
# Total durations = 4 + 5 + 4 + 3 + 3 + 4 = 23.
# There are 5 flights (one flight between each consecutive pair).
# Each flight overlaps one day (the last day of the previous stay),
# so the effective trip length = 23 - 5 = 18 days.
# Therefore, the departure day from the last city must equal 18.

cities = ["Helsinki", "Valencia", "Dubrovnik", "Porto", "Prague", "Reykjavik"]
durations = [4, 5, 4, 3, 3, 4]
n = len(cities)
total_trip = 18

solver = Solver()

# Decision variables:
# pos[i] indicates the index of the city visited in the i-th position.
# They form a permutation of indices 0...5.
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

# Chain the arrival times:
# When finishing a city's stay, you take a flight that overlaps the last day of that stay.
# So, for i >= 1: S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights between consecutive cities:
# • Helsinki and Prague
# • Prague and Valencia
# • Valencia and Porto
# • Helsinki and Reykjavik
# • Dubrovnik and Helsinki
# • Reykjavik and Prague
#
# Map indices:
# 0: Helsinki, 1: Valencia, 2: Dubrovnik, 3: Porto, 4: Prague, 5: Reykjavik

allowed_flights = {
    # Helsinki and Prague
    (0,4), (4,0),
    # Prague and Valencia
    (4,1), (1,4),
    # Valencia and Porto
    (1,3), (3,1),
    # Helsinki and Reykjavik
    (0,5), (5,0),
    # Dubrovnik and Helsinki
    (2,0), (0,2),
    # Reykjavik and Prague
    (5,4), (4,5)
}

for i in range(n-1):
    flight_options = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                flight_options.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(flight_options))

# Special event constraint for Porto:
# For the city Porto (index 3) the visit lasts 3 days (from S to S+2).
# We want the visit to include a day between 16 and 18.
# This is equivalent to requiring: S <= 18 and S + 2 >= 16.
for i in range(n):
    solver.add(If(pos[i] == 3, And(S[i] <= 18, S[i] + 2 >= 16), True))

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
    
    final_day = m.evaluate(S[n-1] + durations[ itinerary[-1] ] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")