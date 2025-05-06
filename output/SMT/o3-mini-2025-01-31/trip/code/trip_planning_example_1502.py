from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# 0: Santorini – 3 days.
# 1: Valencia   – 4 days.
# 2: Madrid     – 2 days.
#      Event: Annual show in Madrid between day 6 and day 7.
# 3: Seville    – 2 days.
# 4: Bucharest  – 3 days.
# 5: Vienna     – 4 days.
#      Event: Wedding in Vienna between day 3 and day 6.
# 6: Riga       – 4 days.
#      Event: Conference in Riga between day 20 and day 23.
# 7: Tallinn    – 5 days.
#      Event: Workshop in Tallinn between day 23 and day 27.
# 8: Krakow     – 5 days.
#      Event: Meet friends in Krakow between day 11 and day 15.
# 9: Frankfurt  – 4 days.
#
# Total planned days = 3+4+2+2+3+4+4+5+5+4 = 36.
# There are 9 flight transitions, so effective trip duration = 36 - 9 = 27 days.
#
# Notes:
# - The trip starts on day 1.
# - In the first city you use the full planned duration.
# - In subsequent cities one day is “lost” due to the flight (effective stay = planned duration - 1).
# -----------------------------------------------------------------------------

cities    = ["Santorini", "Valencia", "Madrid", "Seville", "Bucharest",
             "Vienna", "Riga", "Tallinn", "Krakow", "Frankfurt"]
durations = [3,           4,         2,       2,         3,
             4,         4,         5,      5,       4]

# Event windows: mapping from city index to (event_start, event_end)
events = {
    2: (6, 7),   # Madrid: annual show between day 6 and 7.
    5: (3, 6),   # Vienna: wedding between day 3 and 6.
    6: (20, 23), # Riga: conference between day 20 and 23.
    7: (23, 27), # Tallinn: workshop between day 23 and 27.
    8: (11,15)   # Krakow: meet friends between day 11 and 15.
}

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional unless noted otherwise):
#
# The provided flight connections (with city indices):
#
# 1. Vienna and Bucharest    -> (5,4) and (4,5)
# 2. Santorini and Madrid      -> (0,2) and (2,0)
# 3. Seville and Valencia      -> (3,1) and (1,3)
# 4. Vienna and Seville        -> (5,3) and (3,5)
# 5. Madrid and Valencia       -> (2,1) and (1,2)
# 6. Bucharest and Riga        -> (4,6) and (6,4)
# 7. Valencia and Bucharest    -> (1,4) and (4,1)
# 8. Santorini and Bucharest   -> (0,4) and (4,0)
# 9. Vienna and Valencia       -> (5,1) and (1,5)
#10. Vienna and Madrid         -> (5,2) and (2,5)
#11. Valencia and Krakow       -> (1,8) and (8,1)
#12. Valencia and Frankfurt    -> (1,9) and (9,1)
#13. Krakow and Frankfurt      -> (8,9) and (9,8)
#14. Riga and Tallinn          -> (6,7) and (7,6)   # "from Riga to Tallinn" assumed bidirectional
#15. Vienna and Krakow         -> (5,8) and (8,5)
#16. Vienna and Frankfurt      -> (5,9) and (9,5)
#17. Madrid and Seville        -> (2,3) and (3,2)
#18. Santorini and Vienna      -> (0,5) and (5,0)
#19. Vienna and Riga           -> (5,6) and (6,5)
#20. Frankfurt and Tallinn     -> (9,7) and (7,9)
#21. Frankfurt and Bucharest   -> (9,4) and (4,9)
#22. Madrid and Bucharest      -> (2,4) and (4,2)
#23. Frankfurt and Riga        -> (9,6) and (6,9)
#24. Madrid and Frankfurt      -> (2,9) and (9,2)
# -----------------------------------------------------------------------------

allowed_flights = {
    (5,4), (4,5),
    (0,2), (2,0),
    (3,1), (1,3),
    (5,3), (3,5),
    (2,1), (1,2),
    (4,6), (6,4),
    (1,4), (4,1),
    (0,4), (4,0),
    (5,1), (1,5),
    (5,2), (2,5),
    (1,8), (8,1),
    (1,9), (9,1),
    (8,9), (9,8),
    (6,7), (7,6),
    (5,8), (8,5),
    (5,9), (9,5),
    (2,3), (3,2),
    (0,5), (5,0),
    (5,6), (6,5),
    (9,7), (7,9),
    (9,4), (4,9),
    (2,4), (4,2),
    (9,6), (6,9),
    (2,9), (9,2)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We assume the itinerary is an ordering (permutation) of the 10 cities.
# Let:
#   pos[i]  be the city index visited at itinerary position i (i=0,...,9)
#   S[i]    be the arrival day at the city visited at position i.
#
# Constraints:
#   - S[0] = 1.
#   - For position 1: S[1] = S[0] + (full planned duration of city at pos[0]).
#   - For positions i>=2: S[i] = S[i-1] + (duration(city at pos[i-1]) - 1).
#   - Trip end: Departure day from the last city must equal day 27:
#         S[9] + (duration(city at pos[9]) - 1) - 1 = 27.
# -----------------------------------------------------------------------------

n = 10
s = Solver()

# Itinerary: a permutation of 0...9.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)  # The trip starts on day 1.
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For the first city: full planned duration is used.
# For each subsequent city, one day is lost to the flight so the effective duration is (planned - 1).
# -----------------------------------------------------------------------------

# For position 1 (first connection):
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
        /* pos[i-1]==9 */ durations[9] - 1))))))))))
        
# Trip end constraint: For the last city (position n-1), effective stay = (duration - 1)
# and departure day = S[n-1] + (duration - 1) - 1 should equal 27.
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
           
s.add(S_days[n-1] + last_eff - 1 == 27)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair of cities in the itinerary, there must be a direct flight.
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
# If a city with an event is visited at itinerary position i, the visit interval
# (from arrival S_days[i] to departure) must overlap the event window.
#
# For the first city: effective interval = [S, S + duration - 1].
# For later cities: effective interval = [S, S + (duration - 1) - 1] because one day for the flight.
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