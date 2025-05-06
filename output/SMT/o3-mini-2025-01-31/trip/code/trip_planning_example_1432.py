from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 10 cities with the following properties:
# 0: Frankfurt  - 4 days, no event.
# 1: Salzburg   - 5 days, no event.
# 2: Athens     - 5 days, with a workshop that must occur between day 14 and day 18.
#                 For its 5‐day visit [S, S+4], require S <= 18 and S+4 >= 14.
# 3: Reykjavik  - 5 days, no event.
# 4: Bucharest  - 3 days, no event.
# 5: Valencia   - 2 days, with an annual show that must occur between day 5 and day 6.
#                 For its 2‐day visit [S, S+1], require S <= 6 and S+1 >= 5.
# 6: Vienna     - 5 days, with a wedding that must occur between day 6 and day 10.
#                 For its 5‐day visit [S, S+4], require S <= 10 and S+4 >= 6.
# 7: Amsterdam  - 3 days, no event.
# 8: Stockholm  - 3 days, with a friend meeting that must occur between day 1 and day 3.
#                 For its 3‐day visit [S, S+2], require S <= 3 and S+2 >= 1.
# 9: Riga       - 3 days, with a conference that must occur between day 18 and day 20.
#                 For its 3‐day visit [S, S+2], require S <= 20 and S+2 >= 18.
#
# Total durations: 4 + 5 + 5 + 5 + 3 + 2 + 5 + 3 + 3 + 3 = 38.
# There are 9 flights between the 10 cities, each flight overlaps one day.
# Effective trip length = 38 - 9 = 29 days.
# Thus, the final departure day must equal 29.

cities    = ["Frankfurt", "Salzburg", "Athens", "Reykjavik", "Bucharest",
             "Valencia", "Vienna", "Amsterdam", "Stockholm", "Riga"]
durations = [4, 5, 5, 5, 3, 2, 5, 3, 3, 3]
n = len(cities)
total_trip = 29

solver = Solver()

# Decision variables:
# pos[i] is the index of the city visited in the i-th position.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] is the arrival day (start day) for the city at position i.
# The trip starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain the arrival times:
# After finishing city at position i-1, the next city is entered on the same day
# as the flight overlap. Thus, for i>=1:
#   S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# Final departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights between consecutive cities.
# We assign indices as:
# 0: Frankfurt, 1: Salzburg, 2: Athens, 3: Reykjavik, 4: Bucharest,
# 5: Valencia, 6: Vienna, 7: Amsterdam, 8: Stockholm, 9: Riga.
#
# The allowed flights are given as follows:
#  - Valencia and Frankfurt          : (5,0) and (0,5)
#  - Vienna and Bucharest             : (6,4) and (4,6)
#  - from Valencia to Athens          : (5,2) only (unidirectional)
#  - Athens and Bucharest             : (2,4) and (4,2)
#  - Riga and Frankfurt               : (9,0) and (0,9)
#  - Stockholm and Athens             : (8,2) and (2,8)
#  - Amsterdam and Bucharest          : (7,4) and (4,7)
#  - from Athens to Riga              : (2,9) only (unidirectional)
#  - Amsterdam and Frankfurt          : (7,0) and (0,7)
#  - Stockholm and Vienna             : (8,6) and (6,8)
#  - Vienna and Riga                  : (6,9) and (9,6)
#  - Amsterdam and Reykjavik          : (7,3) and (3,7)
#  - Reykjavik and Frankfurt          : (3,0) and (0,3)
#  - Stockholm and Amsterdam          : (8,7) and (7,8)
#  - Amsterdam and Valencia           : (7,5) and (5,7)
#  - Vienna and Frankfurt             : (6,0) and (0,6)
#  - Valencia and Bucharest           : (5,4) and (4,5)
#  - Bucharest and Frankfurt          : (4,0) and (0,4)
#  - Stockholm and Frankfurt          : (8,0) and (0,8)
#  - Valencia and Vienna              : (5,6) and (6,5)
#  - from Reykjavik to Athens         : (3,2) only (unidirectional)
#  - Frankfurt and Salzburg           : (0,1) and (1,0)
#  - Amsterdam and Vienna             : (7,6) and (6,7)
#  - Stockholm and Reykjavik          : (8,3) and (3,8)
#  - Amsterdam and Riga               : (7,9) and (9,7)
#  - Stockholm and Riga               : (8,9) and (9,8)
#  - Vienna and Reykjavik             : (6,3) and (3,6)
#  - Amsterdam and Athens             : (7,2) and (2,7)
#  - Athens and Frankfurt             : (2,0) and (0,2)
#  - Vienna and Athens                : (6,2) and (2,6)
#  - Riga and Bucharest               : (9,4) and (4,9)
allowed_flights = {
    (5,0), (0,5),
    (6,4), (4,6),
    (5,2),              # from Valencia to Athens (unidirectional)
    (2,4), (4,2),
    (9,0), (0,9),
    (8,2), (2,8),
    (7,4), (4,7),
    (2,9),              # from Athens to Riga (unidirectional)
    (7,0), (0,7),
    (8,6), (6,8),
    (6,9), (9,6),
    (7,3), (3,7),
    (3,0), (0,3),
    (8,7), (7,8),
    (7,5), (5,7),
    (6,0), (0,6),
    (5,4), (4,5),
    (4,0), (0,4),
    (8,0), (0,8),
    (5,6), (6,5),
    (3,2),              # from Reykjavik to Athens (unidirectional)
    (0,1), (1,0),
    (7,6), (6,7),
    (8,3), (3,8),
    (7,9), (9,7),
    (8,9), (9,8),
    (6,3), (3,6),
    (7,2), (2,7),
    (2,0), (0,2),
    (6,2), (2,6),
    (9,4), (4,9)
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
    # Athens (index 2): Workshop must occur between day 14 and day 18.
    # For a 5-day visit [S, S+4]: require S <= 18 and S+4 >= 14.
    solver.add(If(pos[i] == 2, And(S[i] <= 18, S[i] + 4 >= 14), True))
    
    # Valencia (index 5): Annual show between day 5 and day 6.
    # For a 2-day visit [S, S+1]: require S <= 6 and S+1 >= 5.
    solver.add(If(pos[i] == 5, And(S[i] <= 6, S[i] + 1 >= 5), True))
    
    # Vienna (index 6): Wedding between day 6 and day 10.
    # For a 5-day visit [S, S+4]: require S <= 10 and S+4 >= 6.
    solver.add(If(pos[i] == 6, And(S[i] <= 10, S[i] + 4 >= 6), True))
    
    # Stockholm (index 8): Meet a friend between day 1 and day 3.
    # For a 3-day visit [S, S+2]: require S <= 3 and S+2 >= 1.
    solver.add(If(pos[i] == 8, And(S[i] <= 3, S[i] + 2 >= 1), True))
    
    # Riga (index 9): Conference between day 18 and day 20.
    # For a 3-day visit [S, S+2]: require S <= 20 and S+2 >= 18.
    solver.add(If(pos[i] == 9, And(S[i] <= 20, S[i] + 2 >= 18), True))

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