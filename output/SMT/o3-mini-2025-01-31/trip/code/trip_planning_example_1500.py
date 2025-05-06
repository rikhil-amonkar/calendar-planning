from z3 import Solver, Int, IntVector, And, Or, If, Distinct, Sum, sat

# We have 10 cities with specified durations and special event requirements:
#
# City indices, durations, and events:
#  0: Zurich     - 2 days; conference must be attended during day 7 and 8
#                    For a 2‐day visit [S, S+1] to cover both day7 and day8, we need S == 7.
#  1: Bucharest  - 2 days; no extra event.
#  2: Hamburg    - 5 days; no extra event.
#  3: Barcelona  - 4 days; no extra event.
#  4: Reykjavik  - 5 days; visit relatives event between day 9 and day 13.
#                    For visit interval [S, S+4] to intersect [9,13] we require: S <= 13 and S+4 >= 9.
#  5: Stuttgart  - 5 days; no extra event.
#  6: Stockholm  - 2 days; no extra event.
#  7: Tallinn    - 4 days; no extra event.
#  8: Milan      - 5 days; meet friends event between day 3 and day 7.
#                    For visit interval [S, S+4] to intersect [3,7] it suffices to require S <= 7.
#  9: London     - 3 days; annual show from day 1 to day 3.
#                    For visit interval [S, S+2] to cover that, we require S <= 3.
#
# Total planned days computed with overlap: (sum of durations) - (# flights) = (2+2+5+4+5+5+2+4+5+3) - 9
# = 37 - 9 = 28 days.
#
# Allowed direct flights:
#  (Using indices as above: 0:Zurich,1:Bucharest,2:Hamburg,3:Barcelona,4:Reykjavik,5:Stuttgart,
#                         6:Stockholm,7:Tallinn,8:Milan,9:London)
#
#  1. London and Hamburg:          (9,2) and (2,9)
#  2. London and Reykjavik:        (9,4) and (4,9)
#  3. Milan and Barcelona:         (8,3) and (3,8)
#  4. Reykjavik and Barcelona:     (4,3) and (3,4)
#  5. from Reykjavik to Stuttgart: (4,5) only (directed)
#  6. Stockholm and Reykjavik:     (6,4) and (4,6)
#  7. London and Stuttgart:        (9,5) and (5,9)
#  8. Milan and Zurich:            (8,0) and (0,8)
#  9. London and Barcelona:        (9,3) and (3,9)
# 10. Stockholm and Hamburg:       (6,2) and (2,6)
# 11. Zurich and Barcelona:        (0,3) and (3,0)
# 12. Stockholm and Stuttgart:     (6,5) and (5,6)
# 13. Milan and Hamburg:           (8,2) and (2,8)
# 14. Stockholm and Tallinn:       (6,7) and (7,6)
# 15. Hamburg and Bucharest:       (2,1) and (1,2)
# 16. London and Bucharest:        (9,1) and (1,9)
# 17. Milan and Stockholm:         (8,6) and (6,8)
# 18. Stuttgart and Hamburg:       (5,2) and (2,5)
# 19. London and Zurich:           (9,0) and (0,9)
# 20. Milan and Reykjavik:         (8,4) and (4,8)
# 21. London and Stockholm:        (9,6) and (6,9)
# 22. Milan and Stuttgart:         (8,5) and (5,8)
# 23. Stockholm and Barcelona:     (6,3) and (3,6)
# 24. London and Milan:            (9,8) and (8,9)
# 25. Zurich and Hamburg:          (0,2) and (2,0)
# 26. Bucharest and Barcelona:     (1,3) and (3,1)
# 27. Zurich and Stockholm:        (0,6) and (6,0)
# 28. Barcelona and Tallinn:       (3,7) and (7,3)
# 29. Zurich and Tallinn:          (0,7) and (7,0)
# 30. Hamburg and Barcelona:       (2,3) and (3,2)
# 31. Stuttgart and Barcelona:     (5,3) and (3,5)
# 32. Zurich and Reykjavik:        (0,4) and (4,0)
# 33. Zurich and Bucharest:        (0,1) and (1,0)
#
# We now set up the Z3 model.

cities = ["Zurich", "Bucharest", "Hamburg", "Barcelona", "Reykjavik",
          "Stuttgart", "Stockholm", "Tallinn", "Milan", "London"]
durations = [2, 2, 5, 4, 5, 5, 2, 4, 5, 3]
n = len(cities)
total_trip = 28

solver = Solver()

# Decision variables:
# pos[i]: index of city visited in i-th position (all must be distinct)
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i]: arrival day for the city in position i.
S = IntVector("S", n)
solver.add(S[0] == 1)  # trip starts day 1
for i in range(n):
    solver.add(S[i] >= 1)

# Recurrence for arrival times with overlapping flight (each flight "saves" one day)
# For i>=1: S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# Final trip day constraint: last city's departure day equals total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed flights constraints between consecutive cities:
allowed_flights = {
    (9,2), (2,9),                    # London <-> Hamburg
    (9,4), (4,9),                    # London <-> Reykjavik
    (8,3), (3,8),                    # Milan <-> Barcelona
    (4,3), (3,4),                    # Reykjavik <-> Barcelona
    (4,5),                           # from Reykjavik to Stuttgart (directed)
    (6,4), (4,6),                    # Stockholm <-> Reykjavik
    (9,5), (5,9),                    # London <-> Stuttgart
    (8,0), (0,8),                    # Milan <-> Zurich
    (9,3), (3,9),                    # London <-> Barcelona
    (6,2), (2,6),                    # Stockholm <-> Hamburg
    (0,3), (3,0),                    # Zurich <-> Barcelona
    (6,5), (5,6),                    # Stockholm <-> Stuttgart
    (8,2), (2,8),                    # Milan <-> Hamburg
    (6,7), (7,6),                    # Stockholm <-> Tallinn
    (2,1), (1,2),                    # Hamburg <-> Bucharest
    (9,1), (1,9),                    # London <-> Bucharest
    (8,6), (6,8),                    # Milan <-> Stockholm
    (5,2), (2,5),                    # Stuttgart <-> Hamburg
    (9,0), (0,9),                    # London <-> Zurich
    (8,4), (4,8),                    # Milan <-> Reykjavik
    (9,6), (6,9),                    # London <-> Stockholm
    (8,5), (5,8),                    # Milan <-> Stuttgart
    (6,3), (3,6),                    # Stockholm <-> Barcelona
    (9,8), (8,9),                    # London <-> Milan
    (0,2), (2,0),                    # Zurich <-> Hamburg
    (1,3), (3,1),                    # Bucharest <-> Barcelona
    (0,6), (6,0),                    # Zurich <-> Stockholm
    (3,7), (7,3),                    # Barcelona <-> Tallinn
    (0,7), (7,0),                    # Zurich <-> Tallinn
    (2,3), (3,2),                    # Hamburg <-> Barcelona
    (5,3), (3,5),                    # Stuttgart <-> Barcelona
    (0,4), (4,0),                    # Zurich <-> Reykjavik
    (0,1), (1,0)                     # Zurich <-> Bucharest
}

for i in range(n - 1):
    flight_options = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                flight_options.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(flight_options))

# Event constraints for special cities:
for i in range(n):
    # Create boolean flags for each city by index:
    isZurich    = (pos[i] == 0)
    isBucharest = (pos[i] == 1)
    isHamburg   = (pos[i] == 2)
    isBarcelona = (pos[i] == 3)
    isReykjavik = (pos[i] == 4)
    isStuttgart = (pos[i] == 5)
    isStockholm = (pos[i] == 6)
    isTallinn   = (pos[i] == 7)
    isMilan     = (pos[i] == 8)
    isLondon    = (pos[i] == 9)
    
    # Zurich (2 days, conference during day 7 and day 8)
    solver.add(If(isZurich, S[i] == 7, True))
    
    # Reykjavik (5 days, relatives visited between day 9 and 13).
    # Visit interval [S, S+4] must overlap [9,13]:
    # S <= 13 and S+4 >= 9
    solver.add(If(isReykjavik, And(S[i] <= 13, S[i] + 4 >= 9), True))
    
    # Milan (5 days, meet friends event between day 3 and 7).
    # Visit interval [S, S+4] should overlap [3,7]. A sufficient constraint is S <= 7.
    solver.add(If(isMilan, S[i] <= 7, True))
    
    # London (3 days, annual show from day 1 to day 3).
    # Visit interval [S, S+2] should overlap [1,3]. Since S>=1, require S <= 3.
    solver.add(If(isLondon, S[i] <= 3, True))
    
    # Other cities have no additional event constraints.
    
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
        city_name = cities[city_idx]
        arrival = arrivals[i]
        departure = arrival + durations[city_idx] - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")