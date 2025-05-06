from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 6 cities with the following properties:
# Assign indices as follows:
# 0: Mykonos   - 3 days.
# 1: Reykjavik - 2 days, with a wedding between day 9 and day 10.
#                 For a 2‐day visit [S, S+1], we force S == 9.
# 2: Dublin    - 5 days, with an annual show from day 2 to day 6.
#                 For a 5‐day visit [S, S+4], we force S == 2.
# 3: London    - 5 days.
# 4: Helsinki  - 4 days.
# 5: Hamburg   - 2 days, with a friends meeting between day 1 and day 2.
#                 For a 2‐day visit [S, S+1], we force S == 1.
#
# Total durations = 3 + 2 + 5 + 5 + 4 + 2 = 21.
# There are 5 flights between 6 cities (each flight overlaps one day).
# Hence the effective trip length = 21 - 5 = 16 days.
# Thus, the departure day from the last city must equal 16.
#
# Allowed direct flights (bidirectional):
# - Dublin and London      : (2,3) and (3,2)
# - Hamburg and Dublin     : (5,2) and (2,5)
# - Helsinki and Reykjavik : (4,1) and (1,4)
# - Hamburg and London     : (5,3) and (3,5)
# - Dublin and Helsinki    : (2,4) and (4,2)
# - Reykjavik and London   : (1,3) and (3,1)
# - London and Mykonos     : (3,0) and (0,3)
# - Dublin and Reykjavik   : (2,1) and (1,2)
# - Hamburg and Helsinki   : (5,4) and (4,5)
# - Helsinki and London    : (4,3) and (3,4)

cities = ["Mykonos", "Reykjavik", "Dublin", "London", "Helsinki", "Hamburg"]
durations = [3, 2, 5, 5, 4, 2]
n = len(cities)
total_trip = 16

solver = Solver()

# pos[i] represents the index of the city visited at the i-th position.
# These must form a permutation of the cities {0,1,...,5}.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] represents the arrival (start) day for the city in position i.
# The trip always starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain the arrival times:
# When you finish a city's stay, you take a flight that overlaps its final day.
# That is, for i >= 1:
#    S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights constraints between consecutive cities:
allowed_flights = {
    (2,3), (3,2),   # Dublin and London
    (5,2), (2,5),   # Hamburg and Dublin
    (4,1), (1,4),   # Helsinki and Reykjavik
    (5,3), (3,5),   # Hamburg and London
    (2,4), (4,2),   # Dublin and Helsinki
    (1,3), (3,1),   # Reykjavik and London
    (3,0), (0,3),   # London and Mykonos
    (2,1), (1,2),   # Dublin and Reykjavik
    (5,4), (4,5),   # Hamburg and Helsinki
    (4,3), (3,4)    # Helsinki and London
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
    # For Dublin (city index 2): annual show from day 2 to day 6 forces S == 2.
    solver.add(If(pos[i] == 2, S[i] == 2, True))
    # For Reykjavik (city index 1): wedding between day 9 and day 10 forces S == 9.
    solver.add(If(pos[i] == 1, S[i] == 9, True))
    # For Hamburg (city index 5): friends meeting between day 1 and day 2 forces S == 1.
    solver.add(If(pos[i] == 5, S[i] == 1, True))

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
    
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")