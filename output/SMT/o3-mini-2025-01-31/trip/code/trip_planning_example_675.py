from z3 import Solver, Int, IntVector, Distinct, And, Or, If, Sum, sat

# Cities and durations
# 0: Dubrovnik   (4 days)
# 1: Split       (3 days)
# 2: Milan       (3 days)   -- Wedding event between day 11 and day 13 (visit interval [S, S+2] must intersect [11,13])
# 3: Porto       (4 days)
# 4: Krakow      (2 days)   -- Meet friends event between day 8 and day 9 (visit interval [S, S+1] must intersect [8,9])
# 5: Munich      (5 days)   -- Annual show from day 4 to day 8 (visit interval [S, S+4] must intersect [4,8])
cities = ["Dubrovnik", "Split", "Milan", "Porto", "Krakow", "Munich"]
durations = [4, 3, 3, 4, 2, 5]
n = len(cities)

# Total effective trip days calculation:
# Sum(durations) - (n - 1) = (4+3+3+4+2+5) - 5 = 21 - 5 = 16.
total_trip = 16

solver = Solver()

# Decision variables:
# pos[i]: the city index in the i-th position (all different)
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i]: the arrival day for the city in itinerary position i.
S = IntVector("S", n)
# The trip starts on day 1.
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Waiting days: when flying, we "save" one day.
# Our recurrence: for i >= 1, S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + 
               Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# Final trip day constraint:
# Trip ends at S[n-1] + (duration(last) - 1) = total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights between consecutive cities.
# Allowed pairs (bidirectional, unless stated otherwise):
#    Munich <-> Porto       : (5,3) and (3,5)
#    Split <-> Milan        : (1,2) and (2,1)
#    Milan <-> Porto        : (2,3) and (3,2)
#    Munich <-> Krakow      : (5,4) and (4,5)
#    Munich <-> Milan       : (5,2) and (2,5)
#    Dubrovnik <-> Munich   : (0,5) and (5,0)
#    Krakow <-> Split       : (4,1) and (1,4)
#    Krakow <-> Milan       : (4,2) and (2,4)
#    Munich <-> Split       : (5,1) and (1,5)
allowed_flights = {
    (5,3), (3,5),
    (1,2), (2,1),
    (2,3), (3,2),
    (5,4), (4,5),
    (5,2), (2,5),
    (0,5), (5,0),
    (4,1), (1,4),
    (4,2), (2,4),
    (5,1), (1,5)
}

for i in range(n-1):
    flight_options = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                flight_options.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(flight_options))

# Event constraints for cities with special requirements:
for i in range(n):
    # Create booleans for each city event:
    isDubrovnik = (pos[i] == 0)  # no event constraint
    isSplit     = (pos[i] == 1)  # no event constraint
    isMilan     = (pos[i] == 2)  # wedding event between day 11 and 13:
                                  # Visit interval is [S, S+2] so we need S <= 13 and S+2 >= 11, i.e., S in [9, 13].
    isPorto     = (pos[i] == 3)  # no event constraint
    isKrakow    = (pos[i] == 4)  # meet friends event between day 8 and 9:
                                  # Visit interval is [S, S+1] so we need S <= 9 and S+1 >= 8, i.e., S in [7, 9].
    isMunich    = (pos[i] == 5)  # annual show from day 4 to 8:
                                  # Visit interval [S, S+4] must intersect [4,8]. A sufficient condition is S <= 8.
    
    # Milan: wedding event constraint
    solver.add(If(isMilan, And(S[i] >= 9, S[i] <= 13), True))
    
    # Krakow: meet friends event constraint
    solver.add(If(isKrakow, And(S[i] >= 7, S[i] <= 9), True))
    
    # Munich: annual show event constraint
    solver.add(If(isMunich, S[i] <= 8, True))

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
        depart = arrival + durations[city_index] - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrival:2d} | Departure: Day {depart:2d}")
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")