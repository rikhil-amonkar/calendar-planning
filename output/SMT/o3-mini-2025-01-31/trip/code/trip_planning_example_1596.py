from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 10 cities (indices and details):
# 0: Bucharest  – 2 days.
# 1: Krakow     – 4 days.
# 2: Munich     – 3 days.
#                Event: Workshop in Munich between day 18 and day 20.
# 3: Barcelona  – 5 days.
# 4: Warsaw     – 5 days.
#                Event: Conference in Warsaw between day 25 and day 29.
# 5: Budapest   – 5 days.
#                Event: Annual show in Budapest between day 9 and day 13.
# 6: Stockholm  – 2 days.
#                Event: Meet friends in Stockholm between day 17 and day 18.
# 7: Riga       – 5 days.
# 8: Edinburgh  – 5 days.
#                Event: Meet a friend in Edinburgh between day 1 and day 5.
# 9: Vienna     – 5 days.
#
# Total planned days = 2 + 4 + 3 + 5 + 5 + 5 + 2 + 5 + 5 + 5 = 41.
# Since there will be 9 flights (transitions) between 10 cities,
# the effective trip duration = 41 - 9 = 32 days.
#
# Note:
# - In the first city, you enjoy the full duration.
# - In every subsequent city, one day is "lost" due to the flight
#   (so effective stay = duration - 1).
# -----------------------------------------------------------------------------
cities    = ["Bucharest", "Krakow", "Munich", "Barcelona", "Warsaw",
             "Budapest", "Stockholm", "Riga", "Edinburgh", "Vienna"]
durations = [2, 4, 3, 5, 5, 5, 2, 5, 5, 5]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    2: (18, 20),  # Munich: Workshop between day 18 and day 20.
    4: (25, 29),  # Warsaw: Conference between day 25 and day 29.
    5: (9, 13),   # Budapest: Annual show between day 9 and day 13.
    6: (17, 18),  # Stockholm: Meet friends between day 17 and day 18.
    8: (1, 5)     # Edinburgh: Meet a friend between day 1 and day 5.
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# All flights are bidirectional unless noted otherwise.
#
# (City indices as defined above)
#
# 1. Budapest and Munich         -> (Budapest, Munich) and (Munich, Budapest) 
#                                   -> (5,2) and (2,5)
# 2. Bucharest and Riga          -> (Bucharest, Riga) and (Riga, Bucharest)
#                                   -> (0,7) and (7,0)
# 3. Munich and Krakow           -> (Munich, Krakow) and (Krakow, Munich)
#                                   -> (2,1) and (1,2)
# 4. Munich and Warsaw           -> (Munich, Warsaw) and (Warsaw, Munich)
#                                   -> (2,4) and (4,2)
# 5. Munich and Bucharest        -> (Munich, Bucharest) and (Bucharest, Munich)
#                                   -> (2,0) and (0,2)
# 6. Edinburgh and Stockholm     -> (Edinburgh, Stockholm) and (Stockholm, Edinburgh)
#                                   -> (8,6) and (6,8)
# 7. Barcelona and Warsaw        -> (Barcelona, Warsaw) and (Warsaw, Barcelona)
#                                   -> (3,4) and (4,3)
# 8. Edinburgh and Krakow        -> (Edinburgh, Krakow) and (Krakow, Edinburgh)
#                                   -> (8,1) and (1,8)
# 9. Barcelona and Munich        -> (Barcelona, Munich) and (Munich, Barcelona)
#                                   -> (3,2) and (2,3)
# 10. Stockholm and Krakow       -> (Stockholm, Krakow) and (Krakow, Stockholm)
#                                   -> (6,1) and (1,6)
# 11. Budapest and Vienna         -> (Budapest, Vienna) and (Vienna, Budapest)
#                                   -> (5,9) and (9,5)
# 12. Barcelona and Stockholm     -> (Barcelona, Stockholm) and (Stockholm, Barcelona)
#                                   -> (3,6) and (6,3)
# 13. Stockholm and Munich        -> (Stockholm, Munich) and (Munich, Stockholm)
#                                   -> (6,2) and (2,6)
# 14. Edinburgh and Budapest      -> (Edinburgh, Budapest) and (Budapest, Edinburgh)
#                                   -> (8,5) and (5,8)
# 15. Barcelona and Riga          -> (Barcelona, Riga) and (Riga, Barcelona)
#                                   -> (3,7) and (7,3)
# 16. Edinburgh and Barcelona     -> (Edinburgh, Barcelona) and (Barcelona, Edinburgh)
#                                   -> (8,3) and (3,8)
# 17. Vienna and Riga             -> (Vienna, Riga) and (Riga, Vienna)
#                                   -> (9,7) and (7,9)
# 18. Barcelona and Budapest      -> (Barcelona, Budapest) and (Budapest, Barcelona)
#                                   -> (3,5) and (5,3)
# 19. Bucharest and Warsaw        -> (Bucharest, Warsaw) and (Warsaw, Bucharest)
#                                   -> (0,4) and (4,0)
# 20. Vienna and Krakow           -> (Vienna, Krakow) and (Krakow, Vienna)
#                                   -> (9,1) and (1,9)
# 21. Edinburgh and Munich        -> (Edinburgh, Munich) and (Munich, Edinburgh)
#                                   -> (8,2) and (2,8)
# 22. Barcelona and Bucharest     -> (Barcelona, Bucharest) and (Bucharest, Barcelona)
#                                   -> (3,0) and (0,3)
# 23. Edinburgh and Riga          -> (Edinburgh, Riga) and (Riga, Edinburgh)
#                                   -> (8,7) and (7,8)
# 24. Vienna and Stockholm        -> (Vienna, Stockholm) and (Stockholm, Vienna)
#                                   -> (9,6) and (6,9)
# 25. Warsaw and Krakow           -> (Warsaw, Krakow) and (Krakow, Warsaw)
#                                   -> (4,1) and (1,4)
# 26. Barcelona and Krakow        -> (Barcelona, Krakow) and (Krakow, Barcelona)
#                                   -> (3,1) and (1,3)
# 27. from Riga to Munich         -> one-way only: (Riga, Munich)
#                                   -> (7,2)
# 28. Vienna and Bucharest        -> (Vienna, Bucharest) and (Bucharest, Vienna)
#                                   -> (9,0) and (0,9)
# 29. Budapest and Warsaw         -> (Budapest, Warsaw) and (Warsaw, Budapest)
#                                   -> (5,4) and (4,5)
# 30. Vienna and Warsaw           -> (Vienna, Warsaw) and (Warsaw, Vienna)
#                                   -> (9,4) and (4,9)
# 31. Barcelona and Vienna        -> (Barcelona, Vienna) and (Vienna, Barcelona)
#                                   -> (3,9) and (9,3)
# 32. Budapest and Bucharest      -> (Budapest, Bucharest) and (Bucharest, Budapest)
#                                   -> (5,0) and (0,5)
# 33. Vienna and Munich           -> (Vienna, Munich) and (Munich, Vienna)
#                                   -> (9,2) and (2,9)
# 34. Riga and Warsaw             -> (Riga, Warsaw) and (Warsaw, Riga)
#                                   -> (7,4) and (4,7)
# 35. Stockholm and Riga          -> (Stockholm, Riga) and (Riga, Stockholm)
#                                   -> (6,7) and (7,6)
# 36. Stockholm and Warsaw        -> (Stockholm, Warsaw) and (Warsaw, Stockholm)
#                                   -> (6,4) and (4,6)
# -----------------------------------------------------------------------------
allowed_flights = {
    (5,2), (2,5),
    (0,7), (7,0),
    (2,1), (1,2),
    (2,4), (4,2),
    (2,0), (0,2),
    (8,6), (6,8),
    (3,4), (4,3),
    (8,1), (1,8),
    (3,2), (2,3),
    (6,1), (1,6),
    (5,9), (9,5),
    (3,6), (6,3),
    (6,2), (2,6),
    (8,5), (5,8),
    (3,7), (7,3),
    (8,3), (3,8),
    (9,7), (7,9),
    (3,5), (5,3),
    (0,4), (4,0),
    (9,1), (1,9),
    (8,2), (2,8),
    (3,0), (0,3),
    (8,7), (7,8),
    (9,6), (6,9),
    (4,1), (1,4),
    (3,1), (1,3),
    (7,2),         # one-way from Riga to Munich
    (9,0), (0,9),
    (5,4), (4,5),
    (9,4), (4,9),
    (3,9), (9,3),
    (5,0), (0,5),
    (9,2), (2,9),
    (7,4), (4,7),
    (6,7), (7,6),
    (6,4), (4,6)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation (ordering) of the 10 cities:
#   pos[i] : the index of the city visited at itinerary position i, where 0 <= i < 10.
#   S[i]   : the arrival day at the city visited at position i.
#
# In the first city you enjoy the full planned duration: interval = [S, S + duration - 1].
# For every subsequent city, one day is lost due to the flight:
#   effective interval = [S, S + duration - 2].
#
# The departure day from the final city must equal total_trip = 32.
# -----------------------------------------------------------------------------
n = 10
total_trip = 32
s = Solver()

# Permutation variable: each city exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector.
S = IntVector("S", n)
s.add(S[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions for duration expressions at itinerary positions.
def full_duration(i):
    # For the first city.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

def effective_duration(i):
    # For cities at positions i>=1: effective stay = duration - 1.
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#   S[1] = S[0] + (full duration of city at pos[0]).
# For positions i >= 2:
#   S[i] = S[i-1] + (effective duration of city at pos[i-1]).
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the final city (position n-1):
#   Departure = S[n-1] + (duration - 1) - 1 (if not first city) = S[n-1] + duration - 2.
# This must equal total_trip (32).
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair (i, i+1) in the itinerary, there must be a direct flight.
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
# For each city with an event, if visited at itinerary position i the visit interval must
# cover the event window. The interval is:
#   - if i == 0: [S[i], S[i] + duration - 1]
#   - if i >= 1: [S[i], S[i] + duration - 2]
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
        c = itinerary[i]
        city_name = cities[c]
        if i == 0:
            departure = arrivals[i] + durations[c] - 1
        else:
            departure = arrivals[i] + durations[c] - 2
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    
    # Compute trip end.
    last_city = itinerary[n-1]
    if n-1 == 0:
        final_departure = arrivals[n-1] + durations[last_city] - 1
    else:
        final_departure = arrivals[n-1] + durations[last_city] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")