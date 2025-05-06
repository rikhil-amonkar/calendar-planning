from z3 import Solver, Int, IntVector, If, Distinct, And, Or, Sum, sat

# In this problem we have 5 cities with fixed durations and special event requirements.
# The cities (with index, name, duration, and event details) are:
#   0: Reykjavik  - 7 days. (No extra event requirement.)
#   1: Riga       - 2 days. Friend meeting must occur during day 1 and day 2.
#                   For a 2‐day visit [S, S+1] to overlap [1,2], it is sufficient to require S <= 2.
#   2: Warsaw     - 3 days. (No extra event requirement.)
#   3: Istanbul   - 6 days. Wedding event must occur between day 2 and day 7.
#                   For a 6‐day visit [S, S+5] to overlap [2,7], we require S <= 7.
#   4: Krakow     - 7 days. (No extra event requirement.)
#
# The total planned trip days is 21 days.
# Note: The effective trip days equal the sum of durations minus  (# flights). Here: (7+2+3+6+7)-4 = 25-4 = 21.

cities = ["Reykjavik", "Riga", "Warsaw", "Istanbul", "Krakow"]
durations = [7, 2, 3, 6, 7]
n = len(cities)
total_trip = 21

# Allowed direct flights between cities
# Provided flight connections (bidirectional unless noted otherwise):
#   Istanbul and Krakow           -> (3,4) and (4,3)
#   Warsaw and Reykjavik          -> (2,0) and (0,2)
#   Istanbul and Warsaw           -> (3,2) and (2,3)
#   Riga and Istanbul             -> (1,3) and (3,1)
#   Krakow and Warsaw             -> (4,2) and (2,4)
#   Riga and Warsaw               -> (1,2) and (2,1)
allowed_flights = {
    (3,4), (4,3),
    (2,0), (0,2),
    (3,2), (2,3),
    (1,3), (3,1),
    (4,2), (2,4),
    (1,2), (2,1)
}

solver = Solver()

# Decision variables:
# pos[i]: the index of the city visited at the i-th position; we require all be distinct.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i]: the arrival day in the city at itinerary position i.
# The trip starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Transit: When flying from one city to the next, the arrival day of the next city is computed as:
#   S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
# Because we "overlap" the flight day.
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# Final trip day constraint: Departure from the last city must be on day total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed flight constraints between consecutive cities.
for i in range(n - 1):
    flight_options = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                flight_options.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(flight_options))

# Special event constraints:
for i in range(n):
    # Create booleans for each city
    isReykjavik = (pos[i] == 0)  # Reykjavik: no event constraint.
    isRiga      = (pos[i] == 1)  # Riga: friend meeting between day 1 and day 2 => require S <= 2.
    isWarsaw    = (pos[i] == 2)  # Warsaw: no extra event.
    isIstanbul  = (pos[i] == 3)  # Istanbul: wedding between day 2 and day 7 => require S <= 7.
    isKrakow    = (pos[i] == 4)  # Krakow: no extra event.
    
    # Riga event constraint.
    solver.add(If(isRiga, S[i] <= 2, True))
    # Istanbul wedding constraint.
    solver.add(If(isIstanbul, S[i] <= 7, True))
    
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