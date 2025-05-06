from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 8 cities with the following properties:
# 0: Brussels   - 3 days.
# 1: Helsinki   - 3 days.
# 2: Split      - 4 days.
# 3: Dubrovnik  - 2 days.
# 4: Istanbul   - 5 days, with an annual show from day 1 to day 5.
#                      For a 5‐day visit covering days S ... S+4, require S <= 5.
# 5: Milan      - 4 days.
# 6: Vilnius    - 5 days, with a workshop between day 18 and day 22.
#                      For a 5‐day visit covering days S ... S+4, require S <= 22 and S+4 >= 18.
# 7: Frankfurt  - 3 days, with a wedding between day 16 and day 18.
#                      For a 3‐day visit covering days S ... S+2, require S <= 18 and S+2 >= 16.
#
# Total durations = 3+3+4+2+5+4+5+3 = 29.
# We will have 7 flights between 8 cities, each flight “overlaps” one day.
# So the effective trip length is 29 - 7 = 22 days.
# Hence, the final departure day must equal 22.
#
# Allowed direct flights (note the ones marked "from" are one‐direction only):
# 1. Milan and Frankfurt         : (5,7) and (7,5)
# 2. Split and Frankfurt         : (2,7) and (7,2)
# 3. Milan and Split             : (5,2) and (2,5)
# 4. Brussels and Vilnius        : (0,6) and (6,0)
# 5. Brussels and Helsinki       : (0,1) and (1,0)
# 6. Istanbul and Brussels       : (4,0) and (0,4)
# 7. Milan and Vilnius           : (5,6) and (6,5)
# 8. Brussels and Milan          : (0,5) and (5,0)
# 9. Istanbul and Helsinki       : (4,1) and (1,4)
# 10. Helsinki and Vilnius       : (1,6) and (6,1)
# 11. Helsinki and Dubrovnik     : (1,3) and (3,1)
# 12. Split and Vilnius          : (2,6) and (6,2)
# 13. from Dubrovnik to Istanbul : (3,4)   (only this direction)
# 14. Istanbul and Milan         : (4,5) and (5,4)
# 15. Helsinki and Frankfurt     : (1,7) and (7,1)
# 16. Istanbul and Vilnius       : (4,6) and (6,4)
# 17. Split and Helsinki         : (2,1) and (1,2)
# 18. Milan and Helsinki         : (5,1) and (1,5)
# 19. Istanbul and Frankfurt     : (4,7) and (7,4)
# 20. from Brussels to Frankfurt : (0,7)   (only this direction)
# 21. Dubrovnik and Frankfurt    : (3,7) and (7,3)
# 22. Frankfurt and Vilnius      : (7,6) and (6,7)

cities = ["Brussels", "Helsinki", "Split", "Dubrovnik", "Istanbul", "Milan", "Vilnius", "Frankfurt"]
durations = [3, 3, 4, 2, 5, 4, 5, 3]
n = len(cities)
total_trip = 22

solver = Solver()

# Decision variables:
# pos[i] is the index of the city visited at the i-th position.
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

# Chaining arrival days:
# For i>=1, S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# Final departure day must equal total_trip:
# S[n-1] + (duration(last city)-1) == total_trip
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights constraints between consecutive cities:
allowed_flights = {
    (5,7), (7,5),           # Milan <-> Frankfurt
    (2,7), (7,2),           # Split <-> Frankfurt
    (5,2), (2,5),           # Milan <-> Split
    (0,6), (6,0),           # Brussels <-> Vilnius
    (0,1), (1,0),           # Brussels <-> Helsinki
    (4,0), (0,4),           # Istanbul <-> Brussels
    (5,6), (6,5),           # Milan <-> Vilnius
    (0,5), (5,0),           # Brussels <-> Milan
    (4,1), (1,4),           # Istanbul <-> Helsinki
    (1,6), (6,1),           # Helsinki <-> Vilnius
    (1,3), (3,1),           # Helsinki <-> Dubrovnik
    (2,6), (6,2),           # Split <-> Vilnius
    (3,4),                 # from Dubrovnik to Istanbul only
    (4,5), (5,4),           # Istanbul <-> Milan
    (1,7), (7,1),           # Helsinki <-> Frankfurt
    (4,6), (6,4),           # Istanbul <-> Vilnius
    (2,1), (1,2),           # Split <-> Helsinki
    (5,1), (1,5),           # Milan <-> Helsinki
    (4,7), (7,4),           # Istanbul <-> Frankfurt
    (0,7),                 # from Brussels to Frankfurt only
    (3,7), (7,3),           # Dubrovnik <-> Frankfurt
    (7,6), (6,7)            # Frankfurt <-> Vilnius
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
    # Istanbul (index 4): Annual show from day 1 to day 5.
    # For a 5-day visit [S, S+4], require S <= 5.
    solver.add(If(pos[i] == 4, S[i] <= 5, True))
    
    # Vilnius (index 6): Workshop between day 18 and day 22.
    # For a 5-day visit [S, S+4], require S <= 22 and S+4 >= 18.
    solver.add(If(pos[i] == 6, And(S[i] <= 22, S[i] + 4 >= 18), True))
    
    # Frankfurt (index 7): Wedding between day 16 and day 18.
    # For a 3-day visit [S, S+2], require S <= 18 and S+2 >= 16.
    solver.add(If(pos[i] == 7, And(S[i] <= 18, S[i] + 2 >= 16), True))

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