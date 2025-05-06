from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 7 cities with the following properties:
# City indices and durations:
# 0: Paris    - 5 days.
# 1: Florence - 3 days.
# 2: Vienna   - 2 days.
#             Relatives in Vienna between day 19 and day 20.
#             For a 2-day visit [S, S+1] we require: S <= 20 and S+1 >= 19.
# 3: Porto    - 3 days.
#             Workshop in Porto between day 1 and day 3.
#             For a 3-day visit [S, S+2] we require: S <= 3.
# 4: Munich   - 5 days.
# 5: Nice     - 5 days.
# 6: Warsaw   - 3 days.
#             Wedding in Warsaw between day 13 and day 15.
#             For a 3-day visit [S, S+2] we require: S <= 15 and S+2 >= 13.
#
# Total durations = 5 + 3 + 2 + 3 + 5 + 5 + 3 = 26.
# There are 6 flights (between consecutive cities) and each flight re-uses the last day of a stay.
# Hence, effective trip length = 26 - 6 = 20 days.
# So, the departure day from the final city must equal 20.

cities = ["Paris", "Florence", "Vienna", "Porto", "Munich", "Nice", "Warsaw"]
durations = [5, 3, 2, 3, 5, 5, 3]
n = len(cities)
total_trip = 20

solver = Solver()

# Decision variables:
# pos[i] represents the index of the city visited at position i.
# They form a permutation of the indices {0,1,...,6}.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] is the arrival (start) day for the city at position i.
# The trip starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain the arrival times:
# After finishing the stay at the city at pos[i-1], a flight is taken that re-uses the last day.
# So for i >= 1: S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights between consecutive cities:
# Map indices:
# 0: Paris, 1: Florence, 2: Vienna, 3: Porto, 4: Munich, 5: Nice, 6: Warsaw
#
# Flights given:
#  • Florence and Vienna           -> bidirectional: (1,2) and (2,1)
#  • Paris and Warsaw              -> (0,6) and (6,0)
#  • Munich and Vienna             -> (4,2) and (2,4)
#  • Porto and Vienna              -> (3,2) and (2,3)
#  • Warsaw and Vienna             -> (6,2) and (2,6)
#  • from Florence to Munich       -> one-way only: (1,4)
#  • Munich and Warsaw             -> (4,6) and (6,4)
#  • Munich and Nice               -> (4,5) and (5,4)
#  • Paris and Florence            -> (0,1) and (1,0)
#  • Warsaw and Nice               -> (6,5) and (5,6)
#  • Porto and Munich              -> (3,4) and (4,3)
#  • Porto and Nice                -> (3,5) and (5,3)
#  • Paris and Vienna              -> (0,2) and (2,0)
#  • Nice and Vienna               -> (5,2) and (2,5)
#  • Porto and Paris               -> (3,0) and (0,3)
#  • Paris and Nice                -> (0,5) and (5,0)
#  • Paris and Munich              -> (0,4) and (4,0)
#  • Porto and Warsaw              -> (3,6) and (6,3)
allowed_flights = {
    (1,2), (2,1),
    (0,6), (6,0),
    (4,2), (2,4),
    (3,2), (2,3),
    (6,2), (2,6),
    (1,4),      # one-way: Florence -> Munich only
    (4,6), (6,4),
    (4,5), (5,4),
    (0,1), (1,0),
    (6,5), (5,6),
    (3,4), (4,3),
    (3,5), (5,3),
    (0,2), (2,0),
    (5,2), (2,5),
    (3,0), (0,3),
    (0,5), (5,0),
    (0,4), (4,0),
    (3,6), (6,3)
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
    # For Vienna (index 2): Relatives in Vienna between day 19 and day 20.
    # For a 2-day visit [S, S+1] we require: S <= 20 and S+1 >= 19.
    solver.add(If(pos[i] == 2, And(S[i] <= 20, S[i] + 1 >= 19), True))
    
    # For Porto (index 3): Workshop in Porto between day 1 and day 3.
    # For a 3-day visit [S, S+2] we require: S <= 3.
    solver.add(If(pos[i] == 3, S[i] <= 3, True))
    
    # For Warsaw (index 6): Wedding in Warsaw between day 13 and day 15.
    # For a 3-day visit [S, S+2] we require: S <= 15 and S+2 >= 13.
    solver.add(If(pos[i] == 6, And(S[i] <= 15, S[i] + 2 >= 13), True))

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
    
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")