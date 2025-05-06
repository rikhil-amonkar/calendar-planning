from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
#  0: Rome      – 3 days.
#  1: Mykonos   – 2 days.
#       Event: Meet your friends in Mykonos between day 10 and day 11.
#  2: Lisbon    – 2 days.
#  3: Frankfurt – 5 days.
#       Event: Wedding in Frankfurt between day 1 and day 5.
#  4: Nice      – 3 days.
#  5: Stuttgart – 4 days.
#  6: Venice    – 4 days.
#  7: Dublin    – 2 days.
#  8: Bucharest – 2 days.
#  9: Seville   – 5 days.
#       Event: Conference in Seville between day 13 and day 17.
#
# Total planned days = 3 + 2 + 2 + 5 + 3 + 4 + 4 + 2 + 2 + 5 = 32.
# There are 9 flight days (one per transit between consecutive cities).
# Thus, effective trip duration = 32 - 9 = 23 days.
#
# Note:
# - The trip starts on day 1.
# - For the first visited city, the full planned duration is used.
# - For every subsequent city, one day is “lost” as the flight day so the effective
#   stay is (planned duration - 1).
# -----------------------------------------------------------------------------

cities    = ["Rome", "Mykonos", "Lisbon", "Frankfurt", "Nice",
             "Stuttgart", "Venice", "Dublin", "Bucharest", "Seville"]
durations = [3, 2, 2, 5, 3, 4, 4, 2, 2, 5]

# Event windows: dictionary mapping city index -> (event_start, event_end)
events = {
    1: (10, 11),  # Mykonos: meet friends between day 10 and 11.
    3: (1, 5),    # Frankfurt: wedding between day 1 and 5.
    9: (13, 17)   # Seville: conference between day 13 and 17.
}

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional):
#
# The given pairs (each allowed in both directions) are:
#
# 1. Rome and Stuttgart       -> (0,5) and (5,0)
# 2. Venice and Rome          -> (6,0) and (0,6)
# 3. Dublin and Bucharest     -> (7,8) and (8,7)
# 4. Mykonos and Rome         -> (1,0) and (0,1)
# 5. Seville and Lisbon       -> (9,2) and (2,9)
# 6. Frankfurt and Venice     -> (3,6) and (6,3)
# 7. Venice and Stuttgart     -> (6,5) and (5,6)
# 8. Bucharest and Lisbon     -> (8,2) and (2,8)
# 9. Nice and Mykonos         -> (4,1) and (1,4)
#10. Venice and Lisbon        -> (6,2) and (2,6)
#11. Dublin and Lisbon        -> (7,2) and (2,7)
#12. Venice and Nice          -> (6,4) and (4,6)
#13. Rome and Seville         -> (0,9) and (9,0)
#14. Frankfurt and Rome       -> (3,0) and (0,3)
#15. Nice and Dublin          -> (4,7) and (7,4)
#16. Rome and Bucharest       -> (0,8) and (8,0)
#17. Frankfurt and Dublin     -> (3,7) and (7,3)
#18. Rome and Dublin          -> (0,7) and (7,0)
#19. Venice and Dublin        -> (6,7) and (7,6)
#20. Rome and Lisbon          -> (0,2) and (2,0)
#21. Frankfurt and Lisbon     -> (3,2) and (2,3)
#22. Nice and Rome            -> (4,0) and (0,4)
#23. Frankfurt and Nice       -> (3,4) and (4,3)
#24. Frankfurt and Stuttgart  -> (3,5) and (5,3)
#25. Frankfurt and Bucharest  -> (3,8) and (8,3)
#26. Lisbon and Stuttgart     -> (2,5) and (5,2)
#27. Nice and Lisbon          -> (4,2) and (2,4)
#28. Seville and Dublin       -> (9,7) and (7,9)
# -----------------------------------------------------------------------------

allowed_flights = {
    (0,5), (5,0),
    (6,0), (0,6),
    (7,8), (8,7),
    (1,0), (0,1),
    (9,2), (2,9),
    (3,6), (6,3),
    (6,5), (5,6),
    (8,2), (2,8),
    (4,1), (1,4),
    (6,2), (2,6),
    (7,2), (2,7),
    (6,4), (4,6),
    (0,9), (9,0),
    (3,0), (0,3),
    (4,7), (7,4),
    (0,8), (8,0),
    (3,7), (7,3),
    (0,7), (7,0),
    (6,7), (7,6),
    (0,2), (2,0),
    (3,2), (2,3),
    (4,0), (0,4),
    (3,4), (4,3),
    (3,5), (5,3),
    (3,8), (8,3),
    (2,5), (5,2),
    (4,2), (2,4),
    (9,7), (7,9)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We assume an itinerary of 10 cities (0 through 9) which is a permutation.
# pos[i] is the index of the city visited at position i.
# S[i] is the arrival day at the city at position i.
#
# Rules:
#  - Trip starts on day 1, so S[0] = 1.
#  - For the first city at pos[0], the effective stay is the full planned duration.
#  - For each subsequent city (i>=1), a flight day is subtracted, so effective stay = (planned duration - 1).
#  - Thus:
#       S[1] = S[0] + durations[city_at(pos[0])]
#       S[i] = S[i-1] + (durations[city_at(pos[i-1])] - 1) for i>=2.
#  - The trip end constraint: S[9] + (effective stay of last city) - 1 == 23.
# -----------------------------------------------------------------------------

n = 10
s = Solver()

# Itinerary: permutation of 0...9
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector:
S_days = IntVector("S", n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#   S[1] = S[0] + full planned duration of city at pos[0].
# For positions i>=2:
#   S[i] = S[i-1] + (planned duration of city at pos[i-1] - 1).
# -----------------------------------------------------------------------------

# Constraint for position 1:
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

# For positions 2 to 9:
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
        /* pos[i-1] == 9 */ durations[9] - 1))))))　)
    )

# Trip end constraint:
# Effective stay for city at pos[9] (not the first city) = durations[city] - 1.
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
s.add(S_days[n-1] + last_eff - 1 == 23)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair (pos[i], pos[i+1]), a direct flight must exist.
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
# For any city that has an event (per 'events'), if that city is visited at
# itinerary position i then the actual visit interval is:
#    [S_days[i], S_days[i] + effective - 1]
# where effective = durations[city] if i==0 else durations[city]-1.
#
# We require that this interval overlaps the event window [event_start, event_end]:
#    S_days[i] <= event_end  AND  (S_days[i] + effective - 1) >= event_start.
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
        effective = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")