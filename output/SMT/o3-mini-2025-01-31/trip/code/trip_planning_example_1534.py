from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 10 cities:
# 0: Warsaw    – 4 days.
# 1: Venice    – 3 days.
# 2: Vilnius   – 3 days.
# 3: Salzburg  – 4 days.
#              Event: Wedding in Salzburg between day 22 and day 25.
# 4: Amsterdam – 2 days.
# 5: Barcelona – 5 days.
#              Event: Meet friends in Barcelona between day 2 and day 6.
# 6: Paris     – 2 days.
#              Event: Attend a workshop in Paris between day 1 and day 2.
# 7: Hamburg   – 4 days.
#              Event: Attend a conference in Hamburg during day 19 to day 22.
# 8: Florence  – 5 days.
# 9: Tallinn   – 2 days.
#              Event: Meet a friend in Tallinn between day 11 and day 12.
#
# Total planned days = 4+3+3+4+2+5+2+4+5+2 = 34.
# There are 9 transitions (flights), so effective trip duration = 34 - 9 = 25 days.
#
# Notes:
# - The trip starts on day 1.
# - In the first city you use its full planned duration.
# - In every subsequent city, one day is “lost” due to the direct flight.
# -----------------------------------------------------------------------------

cities    = ["Warsaw", "Venice", "Vilnius", "Salzburg", "Amsterdam", 
             "Barcelona", "Paris", "Hamburg", "Florence", "Tallinn"]
durations = [4,        3,       3,         4,         2, 
             5,        2,       4,         5,         2]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    3: (22, 25),   # Salzburg: Wedding between day 22 and 25.
    5: (2, 6),     # Barcelona: Meet friends between day 2 and 6.
    6: (1, 2),     # Paris: Workshop between day 1 and 2.
    7: (19, 22),   # Hamburg: Conference between day 19 and 22.
    9: (11, 12)    # Tallinn: Meet a friend between day 11 and 12.
}

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# Each flight is given as a pair (a, b). Some flights are undirected (bidirectional)
# whereas the ones noted "from X to Y" are one-way.
#
# List of allowed flights:
#  1. Paris and Venice             -> (6,1) and (1,6)
#  2. Barcelona and Amsterdam      -> (5,4) and (4,5)
#  3. Amsterdam and Warsaw         -> (4,0) and (0,4)
#  4. Amsterdam and Vilnius        -> (4,2) and (2,4)
#  5. Barcelona and Warsaw         -> (5,0) and (0,5)
#  6. Warsaw and Venice            -> (0,1) and (1,0)
#  7. Amsterdam and Hamburg        -> (4,7) and (7,4)
#  8. Barcelona and Hamburg        -> (5,7) and (7,5)
#  9. Barcelona and Florence       -> (5,8) and (8,5)
# 10. Barcelona and Venice         -> (5,1) and (1,5)
# 11. Paris and Hamburg            -> (6,7) and (7,6)
# 12. Paris and Vilnius            -> (6,2) and (2,6)
# 13. Paris and Amsterdam          -> (6,4) and (4,6)
# 14. Paris and Florence           -> (6,8) and (8,6)
# 15. Florence and Amsterdam       -> (8,4) and (4,8)
# 16. Vilnius and Warsaw           -> (2,0) and (0,2)
# 17. Barcelona and Tallinn        -> (5,9) and (9,5)
# 18. Paris and Warsaw             -> (6,0) and (0,6)
# 19. Tallinn and Warsaw           -> (9,0) and (0,9)
# 20. from Tallinn to Vilnius      -> (9,2)     [one-way only]
# 21. Amsterdam and Tallinn        -> (4,9) and (9,4)
# 22. Paris and Tallinn            -> (6,9) and (9,6)
# 23. Paris and Barcelona          -> (6,5) and (5,6)
# 24. Venice and Hamburg           -> (1,7) and (7,1)
# 25. Warsaw and Hamburg           -> (0,7) and (7,0)
# 26. Hamburg and Salzburg         -> (7,3) and (3,7)
# 27. Amsterdam and Venice         -> (4,1) and (1,4)
# -----------------------------------------------------------------------------

allowed_flights = {
    (6,1), (1,6),
    (5,4), (4,5),
    (4,0), (0,4),
    (4,2), (2,4),
    (5,0), (0,5),
    (0,1), (1,0),
    (4,7), (7,4),
    (5,7), (7,5),
    (5,8), (8,5),
    (5,1), (1,5),
    (6,7), (7,6),
    (6,2), (2,6),
    (6,4), (4,6),
    (6,8), (8,6),
    (8,4), (4,8),
    (2,0), (0,2),
    (5,9), (9,5),
    (6,0), (0,6),
    (9,0), (0,9),
    (9,2),             # one-way: from Tallinn (9) to Vilnius (2) only
    (4,9), (9,4),
    (6,9), (9,6),
    (6,5), (5,6),
    (1,7), (7,1),
    (0,7), (7,0),
    (7,3), (3,7),
    (4,1), (1,4)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We model an itinerary as an ordering (permutation) of the 10 cities:
#   pos[i] : index of the city visited at itinerary position i, for i = 0,...,9.
#   S[i]   : arrival day for the city at itinerary position i.
#
# Constraints:
#   - S[0] == 1 (trip begins at day 1).
#   - For the first city, effective stay = full planned duration.
#   - For every subsequent city, effective stay = (planned duration - 1).
#   - Departure day of the last city should equal day 25.
#
# For a city at itinerary position i:
#   if i == 0: departure = S[i] + durations[city] - 1.
#   if i >= 1: departure = S[i] + (durations[city] - 1) - 1.
# -----------------------------------------------------------------------------

n = 10
s = Solver()

# Itinerary positions: permutation of 0..n-1.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)  # trip starts at day 1.
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
    /* pos[0]==9 */ durations[9])))))))))
    
# Constraints for positions 2 to n-1:
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

# Trip end constraint:
# For the last city, effective stay = (duration - 1)
# Thus, departure day = S_days[n-1] + (durations - 1) - 1 must equal 25.
last_effective = If(pos[n-1] == 0, durations[0] - 1,
                If(pos[n-1] == 1, durations[1] - 1,
                If(pos[n-1] == 2, durations[2] - 1,
                If(pos[n-1] == 3, durations[3] - 1,
                If(pos[n-1] == 4, durations[4] - 1,
                If(pos[n-1] == 5, durations[5] - 1,
                If(pos[n-1] == 6, durations[6] - 1,
                If(pos[n-1] == 7, durations[7] - 1,
                If(pos[n-1] == 8, durations[8] - 1,
                durations[9] - 1))))))))                
s.add(S_days[n-1] + last_effective - 1 == 25)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair of cities in the itinerary, there must be a direct flight.
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
# For each city that hosts an event, if that city is visited at itinerary position i,
# then the visitation interval (from arrival to departure) must overlap with the event window.
#
# For the first city (i == 0): interval = [S, S + durations[city] - 1].
# For subsequent cities (i >= 1): interval = [S, S + (durations[city] - 1) - 1]
#   which is [S, S + durations[city] - 2].
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
        # Effective stay: full duration for the first city; for subsequent cities, (duration - 1).
        effective = durations[city_index] if i == 0 else durations[city_index] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
        
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")