from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 6 cities with the following properties:
# 0: Mykonos   - 4 days, no specific event.
# 1: Nice      - 3 days, with a conference requiring that the 3‐day visit (days S ... S+2)
#                includes both day 14 and day 16.
#                This forces S = 14 (visit on days 14, 15, 16).
# 2: London    - 2 days, no specific event.
# 3: Copenhagen- 3 days, no specific event.
# 4: Oslo      - 5 days, with a friends meeting event that must occur between day 10 and day 14.
#                For its 5‐day visit [S, S+4], require S <= 14 and S+4 >= 10.
# 5: Tallinn   - 4 days, no specific event.
#
# Total durations = 4 + 3 + 2 + 3 + 5 + 4 = 21 days.
# There will be 5 flights (i.e. 5 overlaps of 1 day each), so the effective trip length is
# 21 - 5 = 16 days.
#
# Allowed direct flights (bidirectional) are:
#  - London and Copenhagen       : (2,3) and (3,2)
#  - Copenhagen and Tallinn      : (3,5) and (5,3)
#  - Tallinn and Oslo            : (5,4) and (4,5)
#  - Mykonos and London          : (0,2) and (2,0)
#  - Oslo and Nice               : (4,1) and (1,4)
#  - London and Nice             : (2,1) and (1,2)
#  - Mykonos and Nice            : (0,1) and (1,0)
#  - London and Oslo             : (2,4) and (4,2)
#  - Copenhagen and Nice         : (3,1) and (1,3)
#  - Copenhagen and Oslo         : (3,4) and (4,3)

cities     = ["Mykonos", "Nice", "London", "Copenhagen", "Oslo", "Tallinn"]
durations  = [4,         3,      2,        3,           5,     4]
n = len(cities)
total_trip = 16

solver = Solver()

# Decision variables:
# pos[i] represents the index of the city visited in the i-th position of the itinerary.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] represents the arrival day for the city in position i.
# The trip starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain arrival days.
# When leaving the city at position i-1, you depart after spending its duration;
# due to flight overlaps the next city is entered on the same day as the departure day.
# Thus, for i>=1:  S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The final departure day (exit day from the last city) should equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights between consecutive cities:
allowed_flights = {
    (2,3), (3,2),  # London <-> Copenhagen
    (3,5), (5,3),  # Copenhagen <-> Tallinn
    (5,4), (4,5),  # Tallinn <-> Oslo
    (0,2), (2,0),  # Mykonos <-> London
    (4,1), (1,4),  # Oslo <-> Nice
    (2,1), (1,2),  # London <-> Nice
    (0,1), (1,0),  # Mykonos <-> Nice
    (2,4), (4,2),  # London <-> Oslo
    (3,1), (1,3),  # Copenhagen <-> Nice
    (3,4), (4,3)   # Copenhagen <-> Oslo
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
    # Nice (index 1) conference: the 3-day visit [S, S+2] must cover day 14 and day 16.
    # This forces S = 14.
    solver.add(If(pos[i] == 1, S[i] == 14, True))
    
    # Oslo (index 4) meeting a friend: for its 5-day visit [S, S+4],
    # the visit must include at least one day between day 10 and day 14.
    # We enforce: S <= 14 and S+4 >= 10.
    solver.add(If(pos[i] == 4, And(S[i] <= 14, S[i] + 4 >= 10), True))

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
        print(f" Position {i+1}: {city:12s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")