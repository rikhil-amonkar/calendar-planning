from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 8 cities:
# 0: Vienna     – 4 days.
# 1: Barcelona  – 2 days.
# 2: Edinburgh  – 4 days.
#      Event: Meet a friend in Edinburgh between day 12 and day 15.
# 3: Krakow     – 3 days.
# 4: Riga       – 4 days.
# 5: Hamburg    – 2 days.
#      Event: Conference in Hamburg during day 10 and day 11.
# 6: Paris      – 2 days.
#      Event: Wedding in Paris between day 1 and day 2.
# 7: Stockholm  – 2 days.
#      Event: Visit relatives in Stockholm between day 15 and day 16.
#
# Total planned days = 4 + 2 + 4 + 3 + 4 + 2 + 2 + 2 = 23.
# There are 7 flight transitions, so effective trip duration = 23 - 7 = 16 days.
#
# Notes:
# - The trip starts on day 1.
# - In the very first city you use the full planned duration.
# - In every subsequent city one day is “lost” due to the flight (effective stay = planned duration - 1).
# -----------------------------------------------------------------------------

cities    = ["Vienna", "Barcelona", "Edinburgh", "Krakow", "Riga", "Hamburg", "Paris", "Stockholm"]
durations = [4,         2,          4,          3,       4,     2,         2,      2]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    2: (12, 15),  # Edinburgh: meet friend between day 12 and day 15.
    5: (10, 11),  # Hamburg: conference between day 10 and day 11.
    6: (1, 2),    # Paris: wedding between day 1 and day 2.
    7: (15, 16)   # Stockholm: visit relatives between day 15 and day 16.
}

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# Provided pairs (if “A and B” then include both (A,B) and (B,A), except for
# “from Riga to Hamburg” which is only one way):
#
# 1. Hamburg and Stockholm         -> (5,7) and (7,5)
# 2. Vienna and Stockholm          -> (0,7) and (7,0)
# 3. Paris and Edinburgh            -> (6,2) and (2,6)
# 4. Riga and Barcelona             -> (4,1) and (1,4)
# 5. Paris and Riga                 -> (6,4) and (4,6)
# 6. Krakow and Barcelona           -> (3,1) and (1,3)
# 7. Edinburgh and Stockholm        -> (2,7) and (7,2)
# 8. Paris and Krakow               -> (6,3) and (3,6)
# 9. Krakow and Stockholm           -> (3,7) and (7,3)
#10. Riga and Edinburgh             -> (4,2) and (2,4)
#11. Barcelona and Stockholm        -> (1,7) and (7,1)
#12. Paris and Stockholm            -> (6,7) and (7,6)
#13. Krakow and Edinburgh           -> (3,2) and (2,3)
#14. Vienna and Hamburg             -> (0,5) and (5,0)
#15. Paris and Hamburg              -> (6,5) and (5,6)
#16. Riga and Stockholm             -> (4,7) and (7,4)
#17. Hamburg and Barcelona          -> (5,1) and (1,5)
#18. Vienna and Barcelona           -> (0,1) and (1,0)
#19. Krakow and Vienna              -> (3,0) and (0,3)
#20. from Riga to Hamburg           -> (4,5)   [one-way only]
#21. Barcelona and Edinburgh        -> (1,2) and (2,1)
#22. Paris and Barcelona            -> (6,1) and (1,6)
#23. Hamburg and Edinburgh          -> (5,2) and (2,5)
#24. Paris and Vienna               -> (6,0) and (0,6)
#25. Vienna and Riga                -> (0,4) and (4,0)
# -----------------------------------------------------------------------------

allowed_flights = {
    (5,7), (7,5),
    (0,7), (7,0),
    (6,2), (2,6),
    (4,1), (1,4),
    (6,4), (4,6),
    (3,1), (1,3),
    (2,7), (7,2),
    (6,3), (3,6),
    (3,7), (7,3),
    (4,2), (2,4),
    (1,7), (7,1),
    (6,7), (7,6),
    (3,2), (2,3),
    (0,5), (5,0),
    (6,5), (5,6),
    (4,7), (7,4),
    (5,1), (1,5),
    (0,1), (1,0),
    (3,0), (0,3),
    (4,5),         # Only from Riga to Hamburg.
    (1,2), (2,1),
    (6,1), (1,6),
    (5,2), (2,5),
    (6,0), (0,6),
    (0,4), (4,0)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We define an itinerary as a permutation of the 8 cities:
#   pos[i] : the city index visited at itinerary position i (i=0,...,7)
#   S[i]   : the arrival day at the city visited at position i.
#
# Constraints:
#   - S[0] = 1 (trip starts on day 1)
#   - For the first city, effective stay = full planned duration.
#   - For each subsequent city, effective stay = (planned duration - 1) because one day is used in transit.
#   - The departure day from the last city must be 16.
# -----------------------------------------------------------------------------

n = 8
s = Solver()

# Define the itinerary permutation.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Define arrival day vector.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1: S[1] = S[0] + (duration of first city).
# For position i (i>=2): S[i] = S[i-1] + (duration of previous city - 1).
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
    /* pos[0]==7 */ durations[7])))))))
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
        /* pos[i-1] ==7 */ durations[7] - 1)))))))
)

# Trip end constraint:
# Departure day from the last city = arrival + effective duration - 1 must equal 16.
last_eff = If(pos[n-1] == 0, durations[0] - 1,
         If(pos[n-1] == 1, durations[1] - 1,
         If(pos[n-1] == 2, durations[2] - 1,
         If(pos[n-1] == 3, durations[3] - 1,
         If(pos[n-1] == 4, durations[4] - 1,
         If(pos[n-1] == 5, durations[5] - 1,
         If(pos[n-1] == 6, durations[6] - 1,
         durations[7] - 1))))))
s.add(S_days[n-1] + last_eff - 1 == 16)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive city pair in the itinerary, there must be a direct flight.
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
# For a city with an event, if it is visited at itinerary position i, then its visit
# interval [arrival, departure] must overlap with the event window.
# For the first city, departure = S + duration - 1.
# For subsequent cities, departure = S + (duration - 1) - 1 (extra day lost for transit).
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