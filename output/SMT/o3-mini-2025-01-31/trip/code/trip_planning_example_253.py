from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 4 cities with the following properties:
# 0: Amsterdam - 3 days, with a workshop event that must take place between day 9 and day 11.
#     For a 3-day visit (days S ... S+2) we require S <= 11 and S+2 >= 9.
# 1: Vienna   - 7 days, no special event.
# 2: Santorini- 4 days, no special event.
# 3: Lyon     - 3 days, with a wedding event between day 7 and day 9.
#     For a 3-day visit (days S ... S+2) we require S <= 9 and S+2 >= 7.
#
# Total durations = 3 + 7 + 4 + 3 = 17.
# There are 3 flights between cities and each flight overlaps one day, so effective trip length = 17 - 3 = 14 days.
#
# The allowed direct flights (bidirectional) are:
# - Vienna and Lyon        : (1,3) and (3,1)
# - Vienna and Santorini   : (1,2) and (2,1)
# - Vienna and Amsterdam   : (1,0) and (0,1)
# - Amsterdam and Santorini: (0,2) and (2,0)
# - Lyon and Amsterdam     : (3,0) and (0,3)

cities     = ["Amsterdam", "Vienna", "Santorini", "Lyon"]
durations  = [3, 7, 4, 3]
n = len(cities)
total_trip = 14

solver = Solver()

# Decision variables:
# pos[i] represents the city visited in the i-th position (0-indexed).
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] stands for the arrival day at the city in position i.
# The trip starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# The chain of arrival days.
# When traveling from the city at position i-1 to position i, the arrival day of the latter is:
# S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The final departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Define allowed direct flights between consecutive cities.
allowed_flights = {
    (1,3), (3,1),   # Vienna <-> Lyon
    (1,2), (2,1),   # Vienna <-> Santorini
    (1,0), (0,1),   # Vienna <-> Amsterdam
    (0,2), (2,0),   # Amsterdam <-> Santorini
    (3,0), (0,3)    # Lyon <-> Amsterdam
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
    # Amsterdam's workshop: must cover some day between day 9 and day 11.
    # For a 3-day visit [S, S+2] in Amsterdam (index 0), ensure S <= 11 and S+2 >= 9.
    solver.add(If(pos[i] == 0, And(S[i] <= 11, S[i] + 2 >= 9), True))
    
    # Lyon's wedding: must cover some day between day 7 and day 9.
    # For a 3-day visit [S, S+2] in Lyon (index 3), ensure S <= 9 and S+2 >= 7.
    solver.add(If(pos[i] == 3, And(S[i] <= 9, S[i] + 2 >= 7), True))

# -----------------------------------------------------------------------------
# Solve the model.
# -----------------------------------------------------------------------------
if solver.check() == sat:
    m = solver.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals  = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city_idx = itinerary[i]
        city = cities[city_idx]
        arrival = arrivals[i]
        departure = arrival + durations[city_idx] - 1
        print(f" Position {i+1}: {city:11s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")