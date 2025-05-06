from z3 import Solver, IntVector, Distinct, And, Or, If, sat, Sum

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 10 cities:
# 0: Istanbul    – 4 days.
# 1: Vienna      – 4 days.
# 2: Riga        – 2 days.
# 3: Brussels    – 2 days.
#                  Event: Attend a wedding in Brussels between day 26 and day 27.
# 4: Madrid      – 4 days.
# 5: Vilnius     – 4 days.
#                  Event: Meet your friends in Vilnius between day 20 and day 23.
# 6: Venice      – 5 days.
#                  Event: Attend a workshop in Venice between day 7 and day 11.
# 7: Geneva      – 4 days.
#                  Event: Visit relatives in Geneva between day 1 and day 4.
# 8: Munich      – 5 days.
# 9: Reykjavik   – 2 days.
#
# Total planned days = 4+4+2+2+4+4+5+4+5+2 = 36.
# There are 9 flight transitions, so the effective trip duration = 36 - 9 = 27 days.
#
# Notes:
# - The trip starts on day 1 in the first city, where you enjoy its full planned duration.
# - In every subsequent city one day is “lost” due to the flight,
#   so the effective stay = (duration - 1) days, with departure computed accordingly.
# -----------------------------------------------------------------------------
cities    = ["Istanbul", "Vienna", "Riga", "Brussels", "Madrid", "Vilnius", "Venice", "Geneva", "Munich", "Reykjavik"]
durations = [4,          4,       2,      2,         4,       4,       5,       4,       5,       2]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    3: (26, 27),  # Brussels: wedding between day 26 and 27.
    5: (20, 23),  # Vilnius: meet friends between day 20 and 23.
    6: (7, 11),   # Venice: workshop between day 7 and 11.
    7: (1, 4)     # Geneva: relatives between day 1 and 4.
}

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# The allowed flights (bidirectional unless "from ... to" indicates a one-way flight)
# are given below, using city indices:
#
# 1. Munich and Vienna         -> (8,1) and (1,8)
# 2. Istanbul and Brussels     -> (0,3) and (3,0)
# 3. Vienna and Vilnius        -> (1,5) and (5,1)
# 4. Madrid and Munich         -> (4,8) and (8,4)
# 5. Venice and Brussels       -> (6,3) and (3,6)
# 6. Riga and Brussels         -> (2,3) and (3,2)
# 7. Geneva and Istanbul       -> (7,0) and (0,7)
# 8. Munich and Reykjavik      -> (8,9) and (9,8)
# 9. Vienna and Istanbul       -> (1,0) and (0,1)
#10. Riga and Istanbul         -> (2,0) and (0,2)
#11. Reykjavik and Vienna      -> (9,1) and (1,9)
#12. Venice and Munich         -> (6,8) and (8,6)
#13. Madrid and Venice         -> (4,6) and (6,4)
#14. Vilnius and Istanbul      -> (5,0) and (0,5)
#15. Venice and Vienna         -> (6,1) and (1,6)
#16. Venice and Istanbul       -> (6,0) and (0,6)
#17. From Reykjavik to Madrid  -> (9,4) only
#18. From Riga to Munich       -> (2,8) only
#19. Munich and Istanbul       -> (8,0) and (0,8)
#20. Reykjavik and Brussels    -> (9,3) and (3,9)
#21. Vilnius and Brussels      -> (5,3) and (3,5)
#22. From Vilnius to Munich    -> (5,8) only
#23. Madrid and Vienna         -> (4,1) and (1,4)
#24. Vienna and Riga           -> (1,2) and (2,1)
#25. Geneva and Vienna         -> (7,1) and (1,7)
#26. Madrid and Brussels       -> (4,3) and (3,4)
#27. Vienna and Brussels       -> (1,3) and (3,1)
#28. Geneva and Brussels       -> (7,3) and (3,7)
#29. Geneva and Madrid         -> (7,4) and (4,7)
#30. Munich and Brussels       -> (8,3) and (3,8)
#31. Madrid and Istanbul       -> (4,0) and (0,4)
#32. Geneva and Munich         -> (7,8) and (8,7)
#33. From Riga to Vilnius      -> (2,5) only
# -----------------------------------------------------------------------------
allowed_flights = {
    (8,1), (1,8),
    (0,3), (3,0),
    (1,5), (5,1),
    (4,8), (8,4),
    (6,3), (3,6),
    (2,3), (3,2),
    (7,0), (0,7),
    (8,9), (9,8),
    (1,0), (0,1),
    (2,0), (0,2),
    (9,1), (1,9),
    (6,8), (8,6),
    (4,6), (6,4),
    (5,0), (0,5),
    (6,1), (1,6),
    (6,0), (0,6),
    (9,4),         # from Reykjavik to Madrid (one-way)
    (2,8),         # from Riga to Munich (one-way)
    (8,0), (0,8),
    (9,3), (3,9),
    (5,3), (3,5),
    (5,8),         # from Vilnius to Munich (one-way)
    (4,1), (1,4),
    (1,2), (2,1),
    (7,1), (1,7),
    (4,3), (3,4),
    (1,3), (3,1),
    (7,3), (3,7),
    (7,4), (4,7),
    (8,3), (3,8),
    (4,0), (0,4),
    (7,8), (8,7),
    (2,5)          # from Riga to Vilnius (one-way)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We model the itinerary as a permutation (ordering) of the 10 cities:
#   pos[i] : the city visited at itinerary position i (0 <= pos[i] < 10).
#   S[i]   : the arrival day at the city visited at position i.
#
# For the first visited city (i==0): you spend its full planned duration.
# For every subsequent city (i>=1): you lose one day (flight day) so that
#   the effective stay is (duration - 1) days; departure is S[i] + (duration -1) - 1 = S[i] + duration - 2.
#
# The departure day from the final city must be exactly day 27.
# -----------------------------------------------------------------------------
n = 10
total_trip = 27
s = Solver()

# Itinerary positions as a permutation of 0 .. 9.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(pos[i] >= 0, pos[i] < n)

# Arrival days vector.
S = IntVector("S", n)
s.add(S[0] == 1)  # trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# Helper: expression for full planned duration of the city at itinerary position i.
def full_duration(i):
    return Sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

# Helper: expression for effective duration (for non-first cities): duration - 1.
def effective_duration(i):
    return Sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#    S[1] = S[0] + (full duration of city at pos[0])
# For positions i>=2:
#    S[i] = S[i-1] + (effective duration of city at pos[i-1])
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# The departure day from the final city (position n-1) is:
#   if non-first: S[n-1] + (duration - 1) - 1 = S[n-1] + duration - 2.
# This must equal total_trip.
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair of itinerary positions (i and i+1), there must be a direct flight.
# -----------------------------------------------------------------------------
for i in range(n - 1):
    possible_flights = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                possible_flights.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(possible_flights))

# -----------------------------------------------------------------------------
# Event constraints:
#
# For each event city, if that city is visited at position i then its visit interval
# must overlap with the event window.
#
# The visit interval for a city visited at position i is:
#   if i == 0: [S[i], S[i] + (duration) - 1]
#   if i >= 1: [S[i], S[i] + (duration - 1) - 1] = [S[i], S[i] + duration - 2]
# -----------------------------------------------------------------------------
for i in range(n):
    for city, (ev_start, ev_end) in events.items():
        s.add(
            If(pos[i] == city,
               And(
                   S[i] <= ev_end,
                   If(i == 0,
                      S[i] + durations[city] - 1 >= ev_start,
                      S[i] + durations[city] - 2 >= ev_start)
               ),
               True)
        )

# -----------------------------------------------------------------------------
# Solve the scheduling problem.
# -----------------------------------------------------------------------------
if s.check() == sat:
    m = s.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals  = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city_idx = itinerary[i]
        city_name = cities[city_idx]
        # Calculate effective stay:
        if i == 0:
            effective = durations[city_idx]
            departure = arrivals[i] + effective - 1
        else:
            effective = durations[city_idx] - 1
            departure = arrivals[i] + effective - 1
        print(f" Position {i+1:2d}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S[n-1] + effective_duration(n-1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")