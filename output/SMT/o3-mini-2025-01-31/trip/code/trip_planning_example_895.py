from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 7 cities with the following properties:
# City indices and durations:
# 0: Venice    - 3 days.
#              Visit relatives in Venice between day 5 and 7.
#              For a 3‑day visit [S, S+2], require S <= 7 and S+2 >= 5.
# 1: London    - 3 days.
# 2: Lisbon    - 4 days.
# 3: Brussels  - 2 days.
#              Conference in Brussels during day 1 and day 2 forces the visit to start on day 1.
#              (For a 2‑day visit [S, S+1], require S == 1.)
# 4: Reykjavik - 3 days.
# 5: Santorini - 3 days.
# 6: Madrid    - 5 days.
#              Wedding in Madrid between day 7 and day 11,
#              so for a 5‑day visit [S, S+4] we require S <= 11 and S+4 >= 7.
#
# Total durations = 3 + 3 + 4 + 2 + 3 + 3 + 5 = 23.
# There are 6 flights (one flight between each consecutive pair).
# Each flight overlaps (re-uses) the last day of the previous stay, so the effective trip length = 23 - 6 = 17 days.
# Hence, the departure day from the final city must be day 17.

cities = ["Venice", "London", "Lisbon", "Brussels", "Reykjavik", "Santorini", "Madrid"]
durations = [3, 3, 4, 2, 3, 3, 5]
n = len(cities)
total_trip = 17

solver = Solver()

# Decision variables:
# pos[i] indicates the index of the city visited at the i-th position.
# They form a permutation of the indices {0,1,...,6}.
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

# Chain arrival times:
# Given that each city is stayed for 'duration' days and the flight after a city overlaps its final day,
# for every consecutive pair we have:
#   S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights between consecutive cities.
# City mapping:
# 0: Venice, 1: London, 2: Lisbon, 3: Brussels, 4: Reykjavik, 5: Santorini, 6: Madrid
#
# Flights given:
# • Venice and Madrid              -> (0,6) and (6,0)
# • Lisbon and Reykjavik           -> (2,4) and (4,2)
# • Brussels and Venice            -> (3,0) and (0,3)
# • Venice and Santorini           -> (0,5) and (5,0)
# • Lisbon and Venice              -> (2,0) and (0,2)
# • from Reykjavik to Madrid       -> one-way: (4,6)
# • Brussels and London            -> (3,1) and (1,3)
# • Madrid and London              -> (6,1) and (1,6)
# • Santorini and London           -> (5,1) and (1,5)
# • London and Reykjavik           -> (1,4) and (4,1)
# • Brussels and Lisbon            -> (3,2) and (2,3)
# • Lisbon and London              -> (2,1) and (1,2)
# • Lisbon and Madrid              -> (2,6) and (6,2)
# • Madrid and Santorini           -> (6,5) and (5,6)
# • Brussels and Reykjavik         -> (3,4) and (4,3)
# • Brussels and Madrid            -> (3,6) and (6,3)
# • Venice and London              -> (0,1) and (1,0)
allowed_flights = {
    (0,6), (6,0),
    (2,4), (4,2),
    (3,0), (0,3),
    (0,5), (5,0),
    (2,0), (0,2),
    (4,6),         # one-way from Reykjavik to Madrid
    (3,1), (1,3),
    (6,1), (1,6),
    (5,1), (1,5),
    (1,4), (4,1),
    (3,2), (2,3),
    (2,1), (1,2),
    (2,6), (6,2),
    (6,5), (5,6),
    (3,4), (4,3),
    (3,6), (6,3),
    (0,1), (1,0)
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
    # For Brussels (city index 3): conference during day 1 and day 2, so the 2‑day visit must start on day 1.
    solver.add(If(pos[i] == 3, S[i] == 1, True))
    # For Venice (city index 0): relatives in Venice between day 5 and 7.
    # For a 3‑day visit [S, S+2], require S <= 7 and S+2 >= 5.
    solver.add(If(pos[i] == 0, And(S[i] <= 7, S[i] + 2 >= 5), True))
    # For Madrid (city index 6): wedding in Madrid between day 7 and day 11.
    # For a 5‑day visit [S, S+4], require S <= 11 and S+4 >= 7.
    solver.add(If(pos[i] == 6, And(S[i] <= 11, S[i] + 4 >= 7), True))

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