from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
#  0: Lyon       – 3 days.
#  1: Paris      – 5 days.
#  2: Riga       – 2 days.
#  3: Berlin     – 2 days.
#         Event: Wedding in Berlin between day 1 and day 2.
#  4: Stockholm  – 3 days.
#         Event: Annual show in Stockholm from day 20 to day 22.
#  5: Zurich     – 5 days.
#  6: Nice       – 2 days.
#         Event: Workshop in Nice between day 12 and day 13.
#  7: Seville    – 3 days.
#  8: Milan      – 3 days.
#  9: Naples     – 4 days.
#
# Total planned days = 3+5+2+2+3+5+2+3+3+4 = 32.
# There are 9 flight transitions, so effective trip duration = 32 - 9 = 23 days.
#
# Note:
# - The trip starts on day 1.
# - In the first city, you stay the full duration.
# - In each subsequent city, one day is “lost” for the flight so the effective stay is (planned duration - 1).
# -----------------------------------------------------------------------------

cities    = ["Lyon", "Paris", "Riga", "Berlin", "Stockholm", "Zurich", "Nice", "Seville", "Milan", "Naples"]
durations = [3,      5,       2,      2,       3,         5,       2,      3,        3,      4]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    3: (1, 2),    # Berlin: wedding between day 1 and 2.
    4: (20, 22),  # Stockholm: annual show between day 20 and 22.
    6: (12, 13)   # Nice: workshop between day 12 and 13.
}

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional):
#
# Provided pairs (each allowed both ways) are:
#
# 1. Paris and Stockholm      -> (1,4) and (4,1)
# 2. Seville and Paris         -> (7,1) and (1,7)
# 3. Naples and Zurich         -> (9,5) and (5,9)
# 4. Nice and Riga             -> (6,2) and (2,6)
# 5. Berlin and Milan          -> (3,8) and (8,3)
# 6. Paris and Zurich          -> (1,5) and (5,1)
# 7. Paris and Nice            -> (1,6) and (6,1)
# 8. Milan and Paris           -> (8,1) and (1,8)
# 9. Milan and Riga            -> (8,2) and (2,8)
#10. Paris and Lyon            -> (1,0) and (0,1)
#11. Milan and Naples          -> (8,9) and (9,8)
#12. Paris and Riga            -> (1,2) and (2,1)
#13. Berlin and Stockholm      -> (3,4) and (4,3)
#14. Stockholm and Riga        -> (4,2) and (2,4)
#15. Nice and Zurich           -> (6,5) and (5,6)
#16. Milan and Zurich          -> (8,5) and (5,8)
#17. Lyon and Nice             -> (0,6) and (6,0)
#18. Zurich and Stockholm      -> (5,4) and (4,5)
#19. Zurich and Riga           -> (5,2) and (2,5)
#20. Berlin and Naples         -> (3,9) and (9,3)
#21. Milan and Stockholm       -> (8,4) and (4,8)
#22. Berlin and Zurich         -> (3,5) and (5,3)
#23. Milan and Seville         -> (8,7) and (7,8)
#24. Paris and Naples          -> (1,9) and (9,1)
#25. Berlin and Riga           -> (3,2) and (2,3)
#26. Nice and Stockholm        -> (6,4) and (4,6)
#27. Berlin and Paris          -> (3,1) and (1,3)
#28. Nice and Naples           -> (6,9) and (9,6)
#29. Berlin and Nice           -> (3,6) and (6,3)
# -----------------------------------------------------------------------------

allowed_flights = {
    (1,4), (4,1),
    (7,1), (1,7),
    (9,5), (5,9),
    (6,2), (2,6),
    (3,8), (8,3),
    (1,5), (5,1),
    (1,6), (6,1),
    (8,1), (1,8),
    (8,2), (2,8),
    (1,0), (0,1),
    (8,9), (9,8),
    (1,2), (2,1),
    (3,4), (4,3),
    (4,2), (2,4),
    (6,5), (5,6),
    (8,5), (5,8),
    (0,6), (6,0),
    (5,4), (4,5),
    (5,2), (2,5),
    (3,9), (9,3),
    (8,4), (4,8),
    (3,5), (5,3),
    (8,7), (7,8),
    (1,9), (9,1),
    (3,2), (2,3),
    (6,4), (4,6),
    (3,1), (1,3),
    (6,9), (9,6),
    (3,6), (6,3)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We assume an itinerary of 10 cities (a permutation of indices 0..9) with:
#   pos[i]: the city index visited at position i.
#   S[i]: the arrival day at position i.
#
# Constraints:
#   S[0] = 1.
#   For the first city: S[1] = S[0] + durations[pos[0]].
#   For each subsequent city (i >= 2):
#       S[i] = S[i-1] + (durations[pos[i-1]] - 1)
#   and the trip must end on day 23:
#       S[9] + (durations[pos[9]] - 1) - 1 = 23.
# -----------------------------------------------------------------------------

n = 10
s = Solver()

# Itinerary: permutation of 0...9.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#   S[1] = S[0] + (full planned duration of city at pos[0]).
# For positions 2 to n-1:
#   S[i] = S[i-1] + (duration of city at pos[i-1] - 1).
# -----------------------------------------------------------------------------

def duration_for(city, is_first):
    # if is_first is True, effective duration = full duration, 
    # otherwise, effective duration = duration - 1.
    return durations[city] if is_first else durations[city] - 1

# Constraint for position 1 (first transit):
s.add(
    S_days[1] ==
    If(pos[0] == 0, duration_for(0, True),
    If(pos[0] == 1, duration_for(1, True),
    If(pos[0] == 2, duration_for(2, True),
    If(pos[0] == 3, duration_for(3, True),
    If(pos[0] == 4, duration_for(4, True),
    If(pos[0] == 5, duration_for(5, True),
    If(pos[0] == 6, duration_for(6, True),
    If(pos[0] == 7, duration_for(7, True),
    If(pos[0] == 8, duration_for(8, True),
    /* pos[0] == 9 */ duration_for(9, True))))))))))
)

# For positions 2 to n-1:
for i in range(2, n):
    s.add(
        S_days[i] ==
        S_days[i-1] +
        If(pos[i-1] == 0, duration_for(0, False),
        If(pos[i-1] == 1, duration_for(1, False),
        If(pos[i-1] == 2, duration_for(2, False),
        If(pos[i-1] == 3, duration_for(3, False),
        If(pos[i-1] == 4, duration_for(4, False),
        If(pos[i-1] == 5, duration_for(5, False),
        If(pos[i-1] == 6, duration_for(6, False),
        If(pos[i-1] == 7, duration_for(7, False),
        If(pos[i-1] == 8, duration_for(8, False),
        /* pos[i-1]==9 */ duration_for(9, False))))))))))
    )

# Trip end constraint:
# For the last city (position n-1), effective stay = (duration - 1).
last_effective = If(pos[n-1] == 0, durations[0] - 1,
                  If(pos[n-1] == 1, durations[1] - 1,
                  If(pos[n-1] == 2, durations[2] - 1,
                  If(pos[n-1] == 3, durations[3] - 1,
                  If(pos[n-1] == 4, durations[4] - 1,
                  If(pos[n-1] == 5, durations[5] - 1,
                  If(pos[n-1] == 6, durations[6] - 1,
                  If(pos[n-1] == 7, durations[7] - 1,
                  If(pos[n-1] == 8, durations[8] - 1,
                  durations[9] - 1)))))))))
s.add(S_days[n-1] + last_effective - 1 == 23)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair (pos[i], pos[i+1]), ensure that a direct flight exists.
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
# For any event in a city, if that city is visited at itinerary position i, the visit
# interval is [S_days[i], S_days[i] + effective - 1] (where effective = full duration if i==0,
# otherwise (duration - 1)). The event window must overlap this interval.
#
# That is, for an event with window [ev_start, ev_end]:
#   S_days[i] <= ev_end and (S_days[i] + effective - 1) >= ev_start.
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
        city = itinerary[i]
        city_name = cities[city]
        effective = durations[city] if i == 0 else durations[city] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")