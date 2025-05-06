from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 6 cities with the following properties:
# Indices, City,   Duration,        Special event constraints
# 0: Dublin      - 5 days.
# 1: Helsinki    - 3 days, with a friends meeting between day 3 and day 5.
#    (For a 3‑day stay [S, S+2], require: S <= 5 and S+2 >= 3)
# 2: Riga        - 3 days.
# 3: Reykjavik   - 2 days.
# 4: Vienna      - 2 days, with an annual show from day 2 to day 3.
#    (For a 2‑day stay [S, S+1], we force S == 2 so that the visit is [2,3])
# 5: Tallinn     - 5 days, with a wedding between day 7 and day 11.
#    (For a 5‑day stay [S, S+4], require: S <= 11 and S+4 >= 7)
#
# Total durations = 5 + 3 + 3 + 2 + 2 + 5 = 20.
# There are 5 flights between 6 cities (each flight overlaps one day).
# Hence the effective trip length = 20 - 5 = 15 days.
# The departure day from the last city must equal 15.

cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
durations = [5, 3, 3, 2, 2, 5]
n = len(cities)
total_trip = 15

solver = Solver()

# Decision variables:
# pos[i] represents the index of the city visited in the i-th position.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] represents the arrival (start) day for the city at position i.
# The trip starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain the arrival times using the flight overlap model:
# When finishing city at position i-1 (spending its full duration),
# you take a flight that overlaps the final day;
# that is:
#    S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city equals total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights between consecutive cities.
# City indices:
# 0: Dublin, 1: Helsinki, 2: Riga, 3: Reykjavik, 4: Vienna, 5: Tallinn.
#
# The allowed flights (bidirectional unless noted as unidirectional) are:
# - Helsinki and Riga            : (1,2) and (2,1)
# - from Riga to Tallinn         : (2,5) only (unidirectional)
# - Vienna and Helsinki          : (4,1) and (1,4)
# - Riga and Dublin              : (2,0) and (0,2)
# - Vienna and Riga              : (4,2) and (2,4)
# - Reykjavik and Vienna         : (3,4) and (4,3)
# - Helsinki and Dublin          : (1,0) and (0,1)
# - Tallinn and Dublin           : (5,0) and (0,5)
# - Reykjavik and Helsinki       : (3,1) and (1,3)
# - Reykjavik and Dublin         : (3,0) and (0,3)
# - Helsinki and Tallinn         : (1,5) and (5,1)
# - Vienna and Dublin            : (4,0) and (0,4)
allowed_flights = {
    (1,2), (2,1),
    (2,5),                     # Riga -> Tallinn (unidirectional)
    (4,1), (1,4),
    (2,0), (0,2),
    (4,2), (2,4),
    (3,4), (4,3),
    (1,0), (0,1),
    (5,0), (0,5),
    (3,1), (1,3),
    (3,0), (0,3),
    (1,5), (5,1),
    (4,0), (0,4)
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
    # Helsinki (city 1): friends meeting between day 3 and day 5.
    # For a 3-day stay [S, S+2], require S <= 5 and S+2 >= 3.
    solver.add(If(pos[i] == 1, And(S[i] <= 5, S[i] + 2 >= 3), True))
    
    # Vienna (city 4): annual show from day 2 to day 3.
    # For a 2-day stay [S, S+1], we enforce S == 2.
    solver.add(If(pos[i] == 4, S[i] == 2, True))
    
    # Tallinn (city 5): wedding between day 7 and day 11.
    # For a 5-day stay [S, S+4], require S <= 11 and S+4 >= 7.
    solver.add(If(pos[i] == 5, And(S[i] <= 11, S[i] + 4 >= 7), True))

# -----------------------------------------------------------------------------
# Solve the model.
# -----------------------------------------------------------------------------
if solver.check() == sat:
    m = solver.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    schedule  = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city = cities[itinerary[i]]
        arrival = schedule[i]
        departure = arrival + durations[itinerary[i]] - 1
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")