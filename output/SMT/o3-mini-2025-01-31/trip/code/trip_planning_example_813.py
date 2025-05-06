from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 7 cities with the following properties:
# 0: Seville   - 5 days.
# 1: Vilnius   - 3 days.
# 2: Santorini - 2 days.
# 3: London    - 2 days, with an event: meet friends between day 9 and day 10.
#                     For a 2-day visit [S, S+1] to overlap [9,10],
#                     we require S <= 10 and S+1 >= 9.
# 4: Stuttgart - 3 days, with an event: visit relatives between day 7 and day 9.
#                     For a 3-day visit [S, S+2] to overlap [7,9],
#                     we require S <= 9 and S+2 >= 7.
# 5: Dublin    - 3 days.
# 6: Frankfurt - 5 days.
#
# The sum of the durations is 5+3+2+2+3+3+5 = 23.
# Since there will be 6 flights (7 cities => 6 flights) and we "overlap" one day per flight,
# the effective trip days = 23 - 6 = 17.
# Thus, the trip must end on day 17.
#
# Allowed direct flights (bidirectional):
# - Frankfurt <-> Dublin      : (6,5) and (5,6)
# - Frankfurt <-> London      : (6,3) and (3,6)
# - London <-> Dublin         : (3,5) and (5,3)
# - Vilnius <-> Frankfurt     : (1,6) and (6,1)
# - Frankfurt <-> Stuttgart   : (6,4) and (4,6)
# - Dublin <-> Seville        : (5,0) and (0,5)
# - London <-> Santorini      : (3,2) and (2,3)
# - Stuttgart <-> London      : (4,3) and (3,4)
# - Santorini <-> Dublin      : (2,5) and (5,2)
#
# We will use Z3 to determine an ordering of visiting the cities, and the arrival times,
# such that all flights and event constraints are satisfied, and the trip lasts exactly 17 days.

cities = ["Seville", "Vilnius", "Santorini", "London", "Stuttgart", "Dublin", "Frankfurt"]
durations = [5, 3, 2, 2, 3, 3, 5]
n = len(cities)
total_trip = 17

solver = Solver()

# Decision variables:
# pos[i]: index of the city visited at the i-th position (all distinct).
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i]: arrival day at the city in position i.
# The trip always starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Define arrival days by chaining visits.
# When moving from one city to the next, we "overlap" the flight day.
# That is, for i>=1: S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# Final trip day constraint: departure day of the last city equals total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed flights constraints between consecutive cities:
allowed_flights = {
    (6,5), (5,6),  # Frankfurt <-> Dublin
    (6,3), (3,6),  # Frankfurt <-> London
    (3,5), (5,3),  # London <-> Dublin
    (1,6), (6,1),  # Vilnius <-> Frankfurt
    (6,4), (4,6),  # Frankfurt <-> Stuttgart
    (5,0), (0,5),  # Dublin <-> Seville
    (3,2), (2,3),  # London <-> Santorini
    (4,3), (3,4),  # Stuttgart <-> London
    (2,5), (5,2)   # Santorini <-> Dublin
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
    # London event: meet friends between day 9 and 10.
    # For London (index 3) with 2 days duration: visit covers days S and S+1.
    # To overlap [9,10], we require: S <= 10 and S+1 >= 9.
    solver.add(If(pos[i] == 3, And(S[i] <= 10, S[i] + 1 >= 9), True))
    
    # Stuttgart event: visit relatives between day 7 and 9.
    # For Stuttgart (index 4) with 3 days duration: covers days S...S+2.
    # To overlap [7,9], we require: S <= 9 and S+2 >= 7.
    solver.add(If(pos[i] == 4, And(S[i] <= 9, S[i] + 2 >= 7), True))

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