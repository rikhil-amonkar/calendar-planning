from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 10 cities:
# 0: Valencia – 2 days.
#             Event: Meet friends in Valencia between day 3 and day 4.
# 1: Oslo     – 3 days.
#             Event: Meet a friend in Oslo between day 13 and day 15.
# 2: Lyon     – 4 days.
# 3: Prague   – 3 days.
# 4: Paris    – 4 days.
# 5: Nice     – 4 days.
# 6: Seville  – 5 days.
#             Event: Annual show in Seville from day 5 to day 9.
# 7: Tallinn  – 2 days.
# 8: Mykonos – 5 days.
#             Event: Wedding in Mykonos between day 21 and day 25.
# 9: Lisbon  – 2 days.
#
# Total planned days = 2 + 3 + 4 + 3 + 4 + 4 + 5 + 2 + 5 + 2 = 34.
# There are 9 flight transitions, so effective trip duration = 34 - 9 = 25 days.
#
# Notes:
# - The trip starts on day 1.
# - In the first city, you enjoy its full planned duration.
# - In every subsequent city, one day is "lost" due to the direct flight.
# -----------------------------------------------------------------------------

cities    = ["Valencia", "Oslo", "Lyon", "Prague", "Paris", "Nice", "Seville", "Tallinn", "Mykonos", "Lisbon"]
durations = [2,          3,     4,      3,       4,      4,     5,        2,         5,        2]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    0: (3, 4),     # Valencia: Meet friends between day 3 and 4.
    1: (13, 15),   # Oslo: Meet friend between day 13 and 15.
    6: (5, 9),     # Seville: Annual show from day 5 to 9.
    8: (21, 25)    # Mykonos: Wedding between day 21 and 25.
}

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# Given flights (we assume bidirectional unless noted otherwise):
#
#  1. Lisbon and Paris        -> (9,4) and (4,9)
#  2. Lyon and Nice           -> (2,5) and (5,2)
#  3. Tallinn and Oslo        -> (7,1) and (1,7)
#  4. Prague and Lyon         -> (3,2) and (2,3)
#  5. Paris and Oslo          -> (4,1) and (1,4)
#  6. Lisbon and Seville      -> (9,6) and (6,9)
#  7. Prague and Lisbon       -> (3,9) and (9,3)
#  8. Oslo and Nice           -> (1,5) and (5,1)
#  9. Valencia and Paris      -> (0,4) and (4,0)
# 10. Valencia and Lisbon     -> (0,9) and (9,0)
# 11. Paris and Nice          -> (4,5) and (5,4)
# 12. Nice and Mykonos        -> (5,8) and (8,5)
# 13. Paris and Lyon          -> (4,2) and (2,4)
# 14. Valencia and Lyon       -> (0,2) and (2,0)
# 15. Prague and Oslo         -> (3,1) and (1,3)
# 16. Prague and Paris        -> (3,4) and (4,3)
# 17. Seville and Paris       -> (6,4) and (4,6)
# 18. Oslo and Lyon           -> (1,2) and (2,1)
# 19. Prague and Valencia     -> (3,0) and (0,3)
# 20. Lisbon and Nice         -> (9,5) and (5,9)
# 21. Lisbon and Oslo         -> (9,1) and (1,9)
# 22. Valencia and Seville    -> (0,6) and (6,0)
# 23. Lisbon and Lyon         -> (9,2) and (2,9)
# 24. Paris and Tallinn       -> (4,7) and (7,4)
# 25. Prague and Tallinn      -> (3,7) and (7,3)
# -----------------------------------------------------------------------------

allowed_flights = {
    (9,4), (4,9),
    (2,5), (5,2),
    (7,1), (1,7),
    (3,2), (2,3),
    (4,1), (1,4),
    (9,6), (6,9),
    (3,9), (9,3),
    (1,5), (5,1),
    (0,4), (4,0),
    (0,9), (9,0),
    (4,5), (5,4),
    (5,8), (8,5),
    (4,2), (2,4),
    (0,2), (2,0),
    (3,1), (1,3),
    (3,4), (4,3),
    (6,4), (4,6),
    (1,2), (2,1),
    (3,0), (0,3),
    (9,5), (5,9),
    (9,1), (1,9),
    (0,6), (6,0),
    (9,2), (2,9),
    (4,7), (7,4),
    (3,7), (7,3)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We model an itinerary as a permutation (ordering) of the 10 cities:
#   pos[i] : the index of the city visited at itinerary position i, for i=0,...,9.
#   S[i]   : the arrival day at the city visited at position i.
#
# For a city at position i:
#   If i == 0 (first city): you get the full planned duration.
#       Departure day = S[0] + durations[city] - 1.
#   If i >= 1: effective stay = (durations[city] - 1); 
#       Departure day = S[i] + (durations[city] - 1) - 1.
#
# The departure day of the final city must equal day 25.
# -----------------------------------------------------------------------------

n = 10
s = Solver()

# Itinerary as a permutation of 0 ... n-1.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)  # Trip starts at day 1.
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#   S[1] = S[0] + (full planned duration of city at pos[0]).
# For positions i >= 2:
#   S[i] = S[i-1] + (duration of city at pos[i-1] - 1).
# -----------------------------------------------------------------------------
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
    /* pos[0]==9 */ durations[9])))))))))
    
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
        /* pos[i-1]==9 */ durations[9] - 1))))))))))
    )

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the last city (position n-1), effective stay = (duration - 1),
# so departure day = S_days[n-1] + (duration - 1) - 1 must equal 25.
# -----------------------------------------------------------------------------
last_effective = If(pos[n-1] == 0, durations[0] - 1,
                If(pos[n-1] == 1, durations[1] - 1,
                If(pos[n-1] == 2, durations[2] - 1,
                If(pos[n-1] == 3, durations[3] - 1,
                If(pos[n-1] == 4, durations[4] - 1,
                If(pos[n-1] == 5, durations[5] - 1,
                If(pos[n-1] == 6, durations[6] - 1,
                If(pos[n-1] == 7, durations[7] - 1,
                If(pos[n-1] == 8, durations[8] - 1,
                durations[9] - 1))))))))))
s.add(S_days[n-1] + last_effective - 1 == 25)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair in the itinerary (i to i+1), there must be a direct flight.
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
# If a city with an event is visited at itinerary position i, then the visit interval
# must overlap with the event window.
#
# For position 0: visit interval = [S, S + durations - 1]
# For positions i >= 1: visit interval = [S, S + (durations - 1) - 1] i.e., [S, S + durations - 2]
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
        city_index = itinerary[i]
        city_name = cities[city_index]
        if i == 0:
            effective = durations[city_index]
        else:
            effective = durations[city_index] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")