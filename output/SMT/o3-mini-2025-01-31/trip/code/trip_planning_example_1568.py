from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
#  0: Prague    – 5 days.
#       Event: Annual show from day 5 to day 9.
#  1: Brussels  – 2 days.
#  2: Riga      – 2 days.
#       Event: Meet friends between day 15 and day 16.
#  3: Munich    – 2 days.
#  4: Seville   – 3 days.
#  5: Stockholm – 2 days.
#       Event: Conference between day 16 and day 17.
#  6: Istanbul  – 2 days.
#  7: Amsterdam – 3 days.
#  8: Vienna    – 5 days.
#       Event: Meet a friend between day 1 and day 5.
#  9: Split     – 3 days.
#       Event: Visit relatives between day 11 and day 13.
#
# Total planned days = 5 + 2 + 2 + 2 + 3 + 2 + 2 + 3 + 5 + 3 = 29.
# There are 9 flight days (one per transit between consecutive cities).
# Thus, effective trip duration = 29 - 9 = 20 days.
#
# Note:
# - The trip starts on day 1.
# - In the first visited city, you use the full planned duration.
# - For every subsequent city, a flight day “overlap” reduces the effective stay by 1,
#   so effective stay = (planned duration - 1).
# -----------------------------------------------------------------------------

cities    = ["Prague", "Brussels", "Riga", "Munich", "Seville", "Stockholm", "Istanbul", "Amsterdam", "Vienna", "Split"]
durations = [5,        2,         2,     2,       3,        2,         2,         3,          5,       3]

# Event windows: dictionary mapping city index -> (event_start, event_end)
events = {
    0: (5, 9),    # Prague: annual show between day 5 and 9.
    2: (15, 16),  # Riga: meet friends between day 15 and 16.
    5: (16, 17),  # Stockholm: conference between day 16 and 17.
    8: (1, 5),    # Vienna: meet a friend between day 1 and 5.
    9: (11, 13)   # Split: visit relatives between day 11 and 13.
}

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional):
#
# The provided pairs (each allowed both ways) are:
#
# 1. Riga and Stockholm         -> (2,5) and (5,2)
# 2. Stockholm and Brussels       -> (5,1) and (1,5)
# 3. Istanbul and Munich          -> (6,3) and (3,6)
# 4. Istanbul and Riga            -> (6,2) and (2,6)
# 5. Prague and Split             -> (0,9) and (9,0)
# 6. Vienna and Brussels          -> (8,1) and (1,8)
# 7. Vienna and Riga              -> (8,2) and (2,8)
# 8. Split and Stockholm          -> (9,5) and (5,9)
# 9. Munich and Amsterdam         -> (3,7) and (7,3)
#10. Split and Amsterdam          -> (9,7) and (7,9)
#11. Amsterdam and Stockholm      -> (7,5) and (5,7)
#12. Amsterdam and Riga           -> (7,2) and (2,7)
#13. Vienna and Stockholm         -> (8,5) and (5,8)
#14. Vienna and Istanbul          -> (8,6) and (6,8)
#15. Vienna and Seville           -> (8,4) and (4,8)
#16. Istanbul and Amsterdam       -> (6,7) and (7,6)
#17. Munich and Brussels          -> (3,1) and (1,3)
#18. Prague and Munich            -> (0,3) and (3,0)
#19. Riga and Munich              -> (2,3) and (3,2)
#20. Prague and Amsterdam         -> (0,7) and (7,0)
#21. Prague and Brussels          -> (0,1) and (1,0)
#22. Prague and Istanbul          -> (0,6) and (6,0)
#23. Istanbul and Stockholm       -> (6,5) and (5,6)
#24. Vienna and Prague            -> (8,0) and (0,8)
#25. Munich and Split             -> (3,9) and (9,3)
#26. Vienna and Amsterdam         -> (8,7) and (7,8)
#27. Prague and Stockholm         -> (0,5) and (5,0)
#28. Brussels and Seville         -> (1,4) and (4,1)
#29. Munich and Stockholm         -> (3,5) and (5,3)
#30. Istanbul and Brussels        -> (6,1) and (1,6)
#31. Amsterdam and Seville        -> (7,4) and (4,7)
#32. Vienna and Split             -> (8,9) and (9,8)
#33. Munich and Seville           -> (3,4) and (4,3)
#34. Riga and Brussels            -> (2,1) and (1,2)
#35. Prague and Riga              -> (0,2) and (2,0)
#36. Vienna and Munich            -> (8,3) and (3,8)
# -----------------------------------------------------------------------------

allowed_flights = {
    (2,5), (5,2),
    (5,1), (1,5),
    (6,3), (3,6),
    (6,2), (2,6),
    (0,9), (9,0),
    (8,1), (1,8),
    (8,2), (2,8),
    (9,5), (5,9),
    (3,7), (7,3),
    (9,7), (7,9),
    (7,5), (5,7),
    (7,2), (2,7),
    (8,5), (5,8),
    (8,6), (6,8),
    (8,4), (4,8),
    (6,7), (7,6),
    (3,1), (1,3),
    (0,3), (3,0),
    (2,3), (3,2),
    (0,7), (7,0),
    (0,1), (1,0),
    (0,6), (6,0),
    (6,5), (5,6),
    (8,0), (0,8),
    (3,9), (9,3),
    (8,7), (7,8),
    (0,5), (5,0),
    (1,4), (4,1),
    (3,5), (5,3),
    (6,1), (1,6),
    (7,4), (4,7),
    (8,9), (9,8),
    (3,4), (4,3),
    (2,1), (1,2),
    (0,2), (2,0),
    (8,3), (3,8)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the solver and decision variables.
#
# We assume an itinerary of 10 cities (indices 0 to 9) which is a permutation.
# Let pos[i] be the index of the city visited at itinerary position i.
# Let S[i] be the arrival day for the city at position i.
#
# The constraints are:
#  - S[0] = 1.
#  - For the first city: S[1] = S[0] + duration(city_at(pos[0])).
#  - For positions i>=2: S[i] = S[i-1] + (duration(city_at(pos[i-1])) - 1).
#  - Trip must end on day 20. For the last city (i = n-1), the effective stay is (duration - 1),
#    and we impose: S[n-1] + (duration(last city) - 1) - 1 = 20.
# -----------------------------------------------------------------------------

n = 10
s = Solver()

# Itinerary: pos is a permutation of 0,...,9.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days for each city.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1: arrival day = previous arrival + full planned duration.
# For positions i>=2: arrival day = previous arrival + (planned duration - 1)
# -----------------------------------------------------------------------------

# For position 1:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    If(pos[0] == 4, durations[4],
    If(pos[0] == 5, durations[5],
    If(pos[0] == 6, durations[6],
    If(pos[0] == 7, durations[7],
    If(pos[0] == 8, durations[8],
    /* pos[0] == 9 */ durations[9])))))))))
)

# For positions 2 to n-1:
for i in range(2, n):
    s.add(
        S_days[i] ==
        S_days[i-1] +
        If(pos[i-1] == 0, durations[0] - 1,
        If(pos[i-1] == 1, durations[1] - 1,
        If(pos[i-1] == 2, durations[2] - 1,
        If(pos[i-1] == 3, durations[3] - 1,
        If(pos[i-1] == 4, durations[4] - 1,
        If(pos[i-1] == 5, durations[5] - 1,
        If(pos[i-1] == 6, durations[6] - 1,
        If(pos[i-1] == 7, durations[7] - 1,
        If(pos[i-1] == 8, durations[8] - 1,
        /* pos[i-1]==9 */ durations[9] - 1)))))))))
    )

# Trip end constraint:
# For last city (not the first city) the effective stay is (duration - 1)
last_eff = If(pos[n-1] == 0, durations[0] - 1,
            If(pos[n-1] == 1, durations[1] - 1,
            If(pos[n-1] == 2, durations[2] - 1,
            If(pos[n-1] == 3, durations[3] - 1,
            If(pos[n-1] == 4, durations[4] - 1,
            If(pos[n-1] == 5, durations[5] - 1,
            If(pos[n-1] == 6, durations[6] - 1,
            If(pos[n-1] == 7, durations[7] - 1,
            If(pos[n-1] == 8, durations[8] - 1,
            durations[9] - 1)))))))))
s.add(S_days[n-1] + last_eff - 1 == 20)

# -----------------------------------------------------------------------------
# Direct flight constraints:
#
# For each consecutive pair (pos[i], pos[i+1]), there must be a direct flight.
# -----------------------------------------------------------------------------
for i in range(n - 1):
    flight_options = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                flight_options.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(flight_options))

# -----------------------------------------------------------------------------
# Event constraints:
#
# For any event in a city, if that city is visited at itinerary position i then
# let effective = durations[city] (if i==0) or durations[city]-1 (if i>=1).
# The visit interval is [S_days[i], S_days[i] + effective - 1].
# We require that the event period [event_start, event_end] overlaps the visit interval.
# That is:
#   S_days[i] <= event_end   and   S_days[i] + effective - 1 >= event_start.
# -----------------------------------------------------------------------------
for i in range(n):
    for city, (ev_start, ev_end) in events.items():
        s.add(
            If(pos[i] == city,
               And(
                   S_days[i] <= ev_end,
                   If(i == 0,
                      S_days[i] + durations[city] - 1 >= ev_start,
                      S_days[i] + (durations[city] - 1) - 1 >= ev_start)
               ),
               True)
        )

# -----------------------------------------------------------------------------
# Solve the scheduling problem.
# -----------------------------------------------------------------------------
if s.check() == sat:
    m = s.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals  = [m.evaluate(S_days[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city_name = cities[itinerary[i]]
        # For first city: effective stay is full duration; for subsequent, subtract 1.
        effective = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")