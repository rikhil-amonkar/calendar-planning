from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 5 cities with the following properties:
# 0: Hamburg   - 2 days.
# 1: Zurich    - 3 days, with a wedding in Zurich between day 1 and day 3.
#                For a 3-day visit covering days S ... S+2, to include at least one day in [1,3],
#                we require S <= 3.
# 2: Helsinki  - 2 days.
# 3: Bucharest - 2 days.
# 4: Split     - 7 days, with a conference in Split during day 4 and day 10.
#                For a 7-day visit covering days S ... S+6, to include some day in [4,10]
#                we require S <= 10. (Note: Since S>=1, S+6 is always ≥7, thus S <= 10 is the binding condition.)
#
# The sum of the city durations is: 2 + 3 + 2 + 2 + 7 = 16.
# Since we have 5 cities, there will be 4 flights. We “overlap” the flight day,
# so the effective trip days = 16 - 4 = 12.
# Thus the trip must end on day 12.
#
# Allowed direct flights (bidirectional):
# - Zurich and Helsinki      : (1,2) and (2,1)
# - Hamburg and Bucharest     : (0,3) and (3,0)
# - Helsinki and Hamburg      : (2,0) and (0,2)
# - Zurich and Hamburg        : (1,0) and (0,1)
# - Zurich and Bucharest      : (1,3) and (3,1)
# - Zurich and Split          : (1,4) and (4,1)
# - Helsinki and Split        : (2,4) and (4,2)
# - Split and Hamburg         : (4,0) and (0,4)

cities = ["Hamburg", "Zurich", "Helsinki", "Bucharest", "Split"]
durations = [2, 3, 2, 2, 7]
n = len(cities)
total_trip = 12

solver = Solver()

# Decision variables:
# pos[i] : index of the city visited in the i-th position (all distinct).
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] : the arrival day at the city in position i.
# The trip always starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# When going from one city to the next, the arrival day of the next city is:
# S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# Final departure day constraint:
# The departure day from the last city is S[n-1] + (duration(last city)-1)
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed flights constraints between consecutive cities.
allowed_flights = {
    (1,2), (2,1),  # Zurich <-> Helsinki
    (0,3), (3,0),  # Hamburg <-> Bucharest
    (2,0), (0,2),  # Helsinki <-> Hamburg
    (1,0), (0,1),  # Zurich <-> Hamburg
    (1,3), (3,1),  # Zurich <-> Bucharest
    (1,4), (4,1),  # Zurich <-> Split
    (2,4), (4,2),  # Helsinki <-> Split
    (4,0), (0,4)   # Split <-> Hamburg
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
    # Wedding in Zurich (city index 1) must be attended between day 1 and day 3.
    # For a 3-day visit covering days S ... S+2, ensure that S <= 3.
    solver.add(If(pos[i] == 1, S[i] <= 3, True))
    
    # Conference in Split (city index 4) during day 4 and day 10.
    # For a 7-day visit covering days S ... S+6, ensure that S <= 10.
    solver.add(If(pos[i] == 4, S[i] <= 10, True))
    
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