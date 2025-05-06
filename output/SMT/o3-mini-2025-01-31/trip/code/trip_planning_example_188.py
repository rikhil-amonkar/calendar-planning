from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 3 cities:
# 0: Brussels  - 2 days, and you must attend a conference there during day 1 and day 2.
# 1: Split     - 5 days.
# 2: Barcelona - 7 days.
#
# Effective trip days = (2 + 5 + 7) - (3 - 1) = 14 - 2 = 12.
# So we need the final departure day to be day 12.
#
# Allowed direct flights:
# - Brussels and Barcelona (bidirectional)
# - Barcelona and Split      (bidirectional)
#
# So the order must be such that the consecutive cities are connected by a direct flight.
# The only order that allows Brussels to be visited on day 1 (to satisfy the conference requirement)
# is: Brussels -> Barcelona -> Split.
#
# We now use Z3 to search for an itinerary that meets these conditions.

cities = ["Brussels", "Split", "Barcelona"]
durations = [2, 5, 7]
n = len(cities)
total_trip = 12

solver = Solver()

# pos[i] represents the index of the city visited in the i-th position.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] represents the arrival day at the city in position i.
# The trip always starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# For consecutive visits, the arrival day is defined by 
# S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
# because the flight day overlaps with the departure of the previous stay.
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The final departure day (arrival day + duration - 1) must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed flights constraints between consecutive cities.
# Allowed flights: Brussels <-> Barcelona, and Barcelona <-> Split.
allowed_flights = {
    (0, 2), (2, 0),  # Brussels and Barcelona
    (2, 1), (1, 2)   # Barcelona and Split
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
    # If the city is Brussels (index 0), then the conference occurs on day1 and day2.
    # For a 2-day stay starting at S, the visit covers days S and S+1.
    # Therefore, to cover conference on day 1 and 2, we need S == 1.
    solver.add(If(pos[i] == 0, S[i] == 1, True))
    
# -----------------------------------------------------------------------------
# Solve the model
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