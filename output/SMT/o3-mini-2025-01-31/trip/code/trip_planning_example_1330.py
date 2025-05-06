from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 9 cities with the following properties:
# City indices and durations:
# 0: Salzburg  - 2 days.
# 1: Venice    - 5 days.
# 2: Bucharest - 4 days.
# 3: Brussels  - 2 days, with a friend meeting between day 21 and day 22.
#                 For a 2-day visit [S, S+1] we force S == 21.
# 4: Hamburg   - 4 days.
# 5: Copenhagen- 4 days, with a wedding between day 18 and day 21.
#                 For a 4-day visit [S, S+3] this forces S == 18.
# 6: Nice      - 3 days, with a relatives visit between day 9 and day 11.
#                 For a 3-day visit [S, S+2] we force S == 9.
# 7: Zurich    - 5 days.
# 8: Naples    - 4 days, with a workshop between day 22 and day 25.
#                 For a 4-day visit [S, S+3] we force S == 22.
#
# Total durations = 2 + 5 + 4 + 2 + 4 + 4 + 3 + 5 + 4 = 33.
# There are 8 flights (each flight overlaps one day), so the effective trip length equals 33 - 8 = 25 days.
# Therefore, the departure day from the last city must equal 25.

cities = ["Salzburg", "Venice", "Bucharest", "Brussels", "Hamburg", "Copenhagen", "Nice", "Zurich", "Naples"]
durations = [2, 5, 4, 2, 4, 4, 3, 5, 4]
n = len(cities)
total_trip = 25

solver = Solver()

# Decision variables:
# pos[i] represents the index of the city visited in the i-th position.
# They form a permutation of the indices 0..8.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] represents the arrival (start) day for the city at position i.
# The trip always starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain arrival times using the fact that taking a flight overlaps the last day of a city's stay.
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights between consecutive cities.
# City indices:
# 0: Salzburg, 1: Venice, 2: Bucharest, 3: Brussels, 4: Hamburg,
# 5: Copenhagen, 6: Nice, 7: Zurich, 8: Naples.
# The allowed direct flights (bidirectional unless noted as one-way) are:
allowed_flights = {
    # Zurich and Brussels
    (7,3), (3,7),
    # Bucharest and Copenhagen
    (2,5), (5,2),
    # Venice and Brussels
    (1,3), (3,1),
    # Nice and Zurich
    (6,7), (7,6),
    # Hamburg and Nice
    (4,6), (6,4),
    # Zurich and Naples
    (7,8), (8,7),
    # Hamburg and Bucharest
    (4,2), (2,4),
    # Zurich and Copenhagen
    (7,5), (5,7),
    # Bucharest and Brussels
    (2,3), (3,2),
    # Hamburg and Brussels
    (4,3), (3,4),
    # Venice and Naples
    (1,8), (8,1),
    # Venice and Copenhagen
    (1,5), (5,1),
    # Bucharest and Naples
    (2,8), (8,2),
    # Hamburg and Copenhagen
    (4,5), (5,4),
    # Venice and Zurich
    (1,7), (7,1),
    # Nice and Brussels
    (6,3), (3,6),
    # Hamburg and Venice
    (4,1), (1,4),
    # Copenhagen and Naples
    (5,8), (8,5),
    # Nice and Naples
    (6,8), (8,6),
    # Hamburg and Zurich
    (4,7), (7,4),
    # Salzburg and Hamburg
    (0,4), (4,0),
    # Zurich and Bucharest
    (7,2), (2,7),
    # Brussels and Naples
    (3,8), (8,3),
    # Copenhagen and Brussels
    (5,3), (3,5),
    # Venice and Nice
    (1,6), (6,1),
    # Nice and Copenhagen
    (6,5), (5,6)
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
    # For Brussels (city index 3): meeting friends between day 21 and day 22 forces S == 21.
    solver.add(If(pos[i] == 3, S[i] == 21, True))
    # For Copenhagen (city index 5): wedding between day 18 and day 21 forces S == 18.
    solver.add(If(pos[i] == 5, S[i] == 18, True))
    # For Nice (city index 6): relatives visit between day 9 and day 11 forces S == 9.
    solver.add(If(pos[i] == 6, S[i] == 9, True))
    # For Naples (city index 8): workshop between day 22 and day 25 forces S == 22.
    solver.add(If(pos[i] == 8, S[i] == 22, True))

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