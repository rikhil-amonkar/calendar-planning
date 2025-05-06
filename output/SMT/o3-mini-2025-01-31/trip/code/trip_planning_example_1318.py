from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 9 cities with the following properties:
# 0: Oslo      - 2 days, with a friend meeting that must occur between day 24 and day 25.
#                For its 2‐day visit [S, S+1], require S <= 25 and S+1 >= 24.
# 1: Helsinki  - 2 days, no special event.
# 2: Edinburgh - 3 days, no special event.
# 3: Riga      - 2 days, no special event.
# 4: Tallinn   - 5 days, with a wedding that must occur between day 4 and day 8.
#                For its 5‐day visit [S, S+4], require S <= 8 and S+4 >= 4.
# 5: Budapest  - 5 days, no special event.
# 6: Vilnius   - 5 days, no special event.
# 7: Porto     - 5 days, no special event.
# 8: Geneva    - 4 days, no special event.
#
# Total durations = 2 + 2 + 3 + 2 + 5 + 5 + 5 + 5 + 4 = 33.
# There are 8 flights between the 9 cities, each flight overlaps one day.
# Effective trip length = 33 - 8 = 25 days.
# Thus, the last departure day must equal 25.

cities    = ["Oslo", "Helsinki", "Edinburgh", "Riga", "Tallinn", "Budapest", "Vilnius", "Porto", "Geneva"]
durations = [2,        2,         3,          2,     5,        5,         5,       5,       4]
n = len(cities)
total_trip = 25

solver = Solver()

# Decision variables:
# pos[i] denotes the city (by index) visited in the i-th position (0-indexed).
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

# Linking arrival times: when departing from city at pos[i-1],
# we spend its full duration; however, because flights overlap one day,
# we have: S[i] = S[i-1] + (duration(city at pos[i-1]) - 1).
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city should equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights between consecutive cities.
# City indices:
# 0: Oslo, 1: Helsinki, 2: Edinburgh, 3: Riga, 4: Tallinn,
# 5: Budapest, 6: Vilnius, 7: Porto, 8: Geneva.
#
# The allowed flights are:
#  - Porto and Oslo               : (7,0) and (0,7)
#  - Edinburgh and Budapest       : (2,5) and (5,2)
#  - Edinburgh and Geneva         : (2,8) and (8,2)
#  - from Riga to Tallinn         : (3,4)    [unidirectional]
#  - Edinburgh and Porto          : (2,7) and (7,2)
#  - Vilnius and Helsinki         : (6,1) and (1,6)
#  - from Tallinn to Vilnius      : (4,6)    [unidirectional]
#  - Riga and Oslo                : (3,0) and (0,3)
#  - Geneva and Oslo              : (8,0) and (0,8)
#  - Edinburgh and Oslo           : (2,0) and (0,2)
#  - Edinburgh and Helsinki       : (2,1) and (1,2)
#  - Vilnius and Oslo             : (6,0) and (0,6)
#  - Riga and Helsinki            : (3,1) and (1,3)
#  - Budapest and Geneva          : (5,8) and (8,5)
#  - Helsinki and Budapest        : (1,5) and (5,1)
#  - Helsinki and Oslo            : (1,0) and (0,1)
#  - Edinburgh and Riga           : (2,3) and (3,2)
#  - Tallinn and Helsinki         : (4,1) and (1,4)
#  - Geneva and Porto             : (8,7) and (7,8)
#  - Budapest and Oslo            : (5,0) and (0,5)
#  - Helsinki and Geneva          : (1,8) and (8,1)
#  - from Riga to Vilnius         : (3,6)    [unidirectional]
#  - Tallinn and Oslo             : (4,0) and (0,4)
allowed_flights = {
    (7,0), (0,7),
    (2,5), (5,2),
    (2,8), (8,2),
    (3,4),            # Riga -> Tallinn (unidirectional)
    (2,7), (7,2),
    (6,1), (1,6),
    (4,6),            # Tallinn -> Vilnius (unidirectional)
    (3,0), (0,3),
    (8,0), (0,8),
    (2,0), (0,2),
    (2,1), (1,2),
    (6,0), (0,6),
    (3,1), (1,3),
    (5,8), (8,5),
    (1,5), (5,1),
    (1,0), (0,1),
    (2,3), (3,2),
    (4,1), (1,4),
    (8,7), (7,8),
    (5,0), (0,5),
    (1,8), (8,1),
    (3,6),            # Riga -> Vilnius (unidirectional)
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
    # Oslo (index 0): Friend meeting between day 24 and day 25.
    # 2-day visit [S, S+1] must satisfy: S <= 25 and S+1 >= 24.
    solver.add(If(pos[i] == 0, And(S[i] <= 25, S[i] + 1 >= 24), True))
    
    # Tallinn (index 4): Wedding between day 4 and day 8.
    # 5-day visit [S, S+4] must satisfy: S <= 8 and S+4 >= 4.
    solver.add(If(pos[i] == 4, And(S[i] <= 8, S[i] + 4 >= 4), True))

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