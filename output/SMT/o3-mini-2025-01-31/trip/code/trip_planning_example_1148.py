from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 8 cities with the following specifications:
# 0: Lisbon    - 2 days, with a workshop between day 4 and day 5.
#               For its 2-day visit [S, S+1], require S <= 5 and S+1 >= 4.
# 1: Dubrovnik - 5 days, no special event.
# 2: Copenhagen- 5 days, no special event.
# 3: Prague    - 3 days, no special event.
# 4: Tallinn   - 2 days, with a friend meeting between day 1 and day 2.
#               For its 2-day visit [S, S+1], require S <= 2.
# 5: Stockholm- 4 days, with a wedding between day 13 and day 16.
#               For its 4-day visit [S, S+3], require S <= 16 and S+3 >= 13.
# 6: Split     - 3 days, no special event.
# 7: Lyon      - 2 days, with an annual show between day 18 and day 19.
#               For its 2-day visit [S, S+1], require S <= 19 and S+1 >= 18.
#
# Total durations = 2 + 5 + 5 + 3 + 2 + 4 + 3 + 2 = 26.
# There will be 7 flights between the 8 cities, each overlapping one day,
# so the effective trip length is 26 - 7 = 19 days.
# Thus, the final departure day must equal 19.

# Allowed direct flights (bidirectional) between cities (by their indices):
#  - Dubrovnik and Stockholm      : (1,5) and (5,1)
#  - Lisbon and Copenhagen         : (0,2) and (2,0)
#  - Lisbon and Lyon               : (0,7) and (7,0)
#  - Copenhagen and Stockholm      : (2,5) and (5,2)
#  - Copenhagen and Split          : (2,6) and (6,2)
#  - Prague and Stockholm          : (3,5) and (5,3)
#  - Tallinn and Stockholm         : (4,5) and (5,4)
#  - Prague and Lyon               : (3,7) and (7,3)
#  - Lisbon and Stockholm          : (0,5) and (5,0)
#  - Prague and Lisbon             : (3,0) and (0,3)
#  - Stockholm and Split           : (5,6) and (6,5)
#  - Prague and Copenhagen         : (3,2) and (2,3)
#  - Split and Lyon                : (6,7) and (7,6)
#  - Copenhagen and Dubrovnik      : (2,1) and (1,2)
#  - Prague and Split              : (3,6) and (6,3)
#  - Tallinn and Copenhagen        : (4,2) and (2,4)
#  - Tallinn and Prague            : (4,3) and (3,4)

cities    = ["Lisbon", "Dubrovnik", "Copenhagen", "Prague", "Tallinn", "Stockholm", "Split", "Lyon"]
durations = [2,         5,           5,           3,       2,         4,          3,       2]
n         = len(cities)
total_trip = 19

solver = Solver()

# Decision variables:
# pos[i] will represent the index of the city visited in the i-th position.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] is the arrival day at the city in the i-th position.
# The trip starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain the arrival days:
# When leaving the city at position i-1, you depart after spending its duration.
# Since each flight overlaps one day, for i>=1:
#    S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The final departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights between consecutive cities:
allowed_flights = {
    (1,5), (5,1),         # Dubrovnik <-> Stockholm
    (0,2), (2,0),         # Lisbon <-> Copenhagen
    (0,7), (7,0),         # Lisbon <-> Lyon
    (2,5), (5,2),         # Copenhagen <-> Stockholm
    (2,6), (6,2),         # Copenhagen <-> Split
    (3,5), (5,3),         # Prague <-> Stockholm
    (4,5), (5,4),         # Tallinn <-> Stockholm
    (3,7), (7,3),         # Prague <-> Lyon
    (0,5), (5,0),         # Lisbon <-> Stockholm
    (3,0), (0,3),         # Prague <-> Lisbon
    (5,6), (6,5),         # Stockholm <-> Split
    (3,2), (2,3),         # Prague <-> Copenhagen
    (6,7), (7,6),         # Split <-> Lyon
    (2,1), (1,2),         # Copenhagen <-> Dubrovnik
    (3,6), (6,3),         # Prague <-> Split
    (4,2), (2,4),         # Tallinn <-> Copenhagen
    (4,3), (3,4)          # Tallinn <-> Prague
}

for i in range(n - 1):
    flight_options = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                flight_options.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(flight_options))

# Special event constraints for cities with events:
for i in range(n):
    # Lisbon (index 0): workshop between day 4 and day 5.
    # For a 2-day visit [S, S+1], require S <= 5 and S+1 >= 4.
    solver.add(If(pos[i] == 0, And(S[i] <= 5, S[i] + 1 >= 4), True))
    
    # Tallinn (index 4): meet a friend between day 1 and day 2.
    # For a 2-day visit [S, S+1], require S <= 2.
    solver.add(If(pos[i] == 4, S[i] <= 2, True))
    
    # Stockholm (index 5): wedding between day 13 and day 16.
    # For a 4-day visit [S, S+3], require S <= 16 and S+3 >= 13.
    solver.add(If(pos[i] == 5, And(S[i] <= 16, S[i] + 3 >= 13), True))
    
    # Lyon (index 7): annual show from day 18 to day 19.
    # For a 2-day visit [S, S+1], require S <= 19 and S+1 >= 18.
    solver.add(If(pos[i] == 7, And(S[i] <= 19, S[i] + 1 >= 18), True))

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