from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# There are 8 cities with the following properties:
# 0: Mykonos   - 4 days, with a relatives visit event between day 15 and day 18.
#              For a 4-day visit [S, S+3], require S <= 18 and S+3 >= 15.
# 1: Krakow    - 5 days.
# 2: Vilnius   - 2 days.
# 3: Helsinki  - 2 days.
# 4: Dubrovnik - 3 days, with an annual show event between day 2 and day 4.
#              For a 3-day visit [S, S+2], require S <= 4 and S+2 >= 2.
# 5: Oslo      - 2 days, with a friends meeting event between day 1 and day 2.
#              For a 2-day visit [S, S+1], require S <= 2 and S+1 >= 1.
# 6: Madrid    - 5 days.
# 7: Paris     - 2 days.
#
# Total durations = 4 + 5 + 2 + 2 + 3 + 2 + 5 + 2 = 25 days.
# There will be 7 flights between cities, each flight overlapping one day.
# Hence, the effective trip length is 25 - 7 = 18 days.
# The final departure day must equal 18.

# Allowed direct flights:
# - Oslo and Krakow           : (5,1) and (1,5)
# - Oslo and Paris             : (5,7) and (7,5)
# - Paris and Madrid           : (7,6) and (6,7)
# - Helsinki and Vilnius       : (3,2) and (2,3)
# - Oslo and Madrid            : (5,6) and (6,5)
# - Oslo and Helsinki          : (5,3) and (3,5)
# - Helsinki and Krakow        : (3,1) and (1,3)
# - Dubrovnik and Helsinki     : (4,3) and (3,4)
# - Dubrovnik and Madrid       : (4,6) and (6,4)
# - Oslo and Dubrovnik         : (5,4) and (4,5)
# - Krakow and Paris           : (1,7) and (7,1)
# - Madrid and Mykonos         : (6,0) and (0,6)
# - Oslo and Vilnius           : (5,2) and (2,5)
# - from Krakow to Vilnius     : (1,2) only in this direction
# - Helsinki and Paris         : (3,7) and (7,3)
# - Vilnius and Paris          : (2,7) and (7,2)
# - Helsinki and Madrid        : (3,6) and (6,3)

cities     = ["Mykonos", "Krakow", "Vilnius", "Helsinki", "Dubrovnik", "Oslo", "Madrid", "Paris"]
durations  = [4,          5,        2,         2,         3,           2,     5,       2]
n = len(cities)
total_trip = 18

solver = Solver()

# Decision variables:
# pos[i] is the index of the city visited in the i-th position (0-indexed).
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] is the arrival day at the city in position i.
# The trip starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain the arrival days:
# When finishing the city at position i-1, the next city is entered on the same day as the flight overlap.
# For i>=1: S[i] = S[i-1] + (duration(city_at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# Final departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Define allowed direct flights between consecutive cities:
allowed_flights = {
    (5,1), (1,5),  # Oslo <-> Krakow
    (5,7), (7,5),  # Oslo <-> Paris
    (7,6), (6,7),  # Paris <-> Madrid
    (3,2), (2,3),  # Helsinki <-> Vilnius
    (5,6), (6,5),  # Oslo <-> Madrid
    (5,3), (3,5),  # Oslo <-> Helsinki
    (3,1), (1,3),  # Helsinki <-> Krakow
    (4,3), (3,4),  # Dubrovnik <-> Helsinki
    (4,6), (6,4),  # Dubrovnik <-> Madrid
    (5,4), (4,5),  # Oslo <-> Dubrovnik
    (1,7), (7,1),  # Krakow <-> Paris
    (6,0), (0,6),  # Madrid <-> Mykonos
    (5,2), (2,5),  # Oslo <-> Vilnius
    (1,2),         # from Krakow to Vilnius only (unidirectional)
    (3,7), (7,3),  # Helsinki <-> Paris
    (2,7), (7,2),  # Vilnius <-> Paris
    (3,6), (6,3)   # Helsinki <-> Madrid
}

for i in range(n - 1):
    flights = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                flights.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(flights))

# Special event constraints:
for i in range(n):
    # Mykonos (index 0): relatives visit between day 15 and day 18.
    # For a 4-day visit, [S,S+3] must satisfy: S <= 18 and S+3 >= 15.
    solver.add(If(pos[i] == 0, And(S[i] <= 18, S[i] + 3 >= 15), True))
    
    # Dubrovnik (index 4): annual show between day 2 and day 4.
    # For a 3-day visit, [S,S+2] must satisfy: S <= 4 and S+2 >= 2.
    solver.add(If(pos[i] == 4, And(S[i] <= 4, S[i] + 2 >= 2), True))
    
    # Oslo (index 5): meet friends between day 1 and day 2.
    # For a 2-day visit, [S,S+1] must satisfy: S <= 2 and S+1 >= 1.
    solver.add(If(pos[i] == 5, And(S[i] <= 2, S[i] + 1 >= 1), True))

# -----------------------------------------------------------------------------
# Solve the model.
# -----------------------------------------------------------------------------
if solver.check() == sat:
    m = solver.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals  = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        idx = itinerary[i]
        city = cities[idx]
        arrival = arrivals[i]
        departure = arrival + durations[idx] - 1
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")