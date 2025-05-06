from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 8 cities:
# 0: Dublin    – 5 days.
#      Event: Annual show in Dublin between day 11 and day 15.
# 1: Krakow    – 4 days.
# 2: Istanbul  – 3 days.
#      Event: Meet a friend in Istanbul between day 9 and day 11.
# 3: Venice    – 3 days.
# 4: Naples    – 4 days.
# 5: Brussels  – 2 days.
# 6: Mykonos   – 4 days.
#      Event: Visit relatives in Mykonos between day 1 and day 4.
# 7: Frankfurt – 3 days.
#      Event: Meet your friends in Frankfurt between day 15 and day 17.
#
# Total planned days = 5+4+3+3+4+2+4+3 = 28.
# There are 7 flight transitions, so effective trip duration = 28 - 7 = 21 days.
#
# Notes:
# - The trip starts on day 1.
# - In the very first city you use its full planned duration.
# - In every subsequent city one day is “lost” due to a flight (effective stay = planned duration - 1).
# -----------------------------------------------------------------------------

cities    = ["Dublin", "Krakow", "Istanbul", "Venice", "Naples", "Brussels", "Mykonos", "Frankfurt"]
durations = [5,        4,        3,         3,       4,       2,         4,         3]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    0: (11, 15),  # Dublin: annual show between day 11 and 15.
    2: (9, 11),   # Istanbul: meet a friend between day 9 and 11.
    6: (1, 4),    # Mykonos: visit relatives between day 1 and 4.
    7: (15, 17)   # Frankfurt: meet friends between day 15 and 17.
}

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# Provided pairs (bidirectional unless noted otherwise):
#
# 1. Dublin and Brussels        -> (0,5) and (5,0)
# 2. Mykonos and Naples           -> (6,4) and (4,6)
# 3. Venice and Istanbul          -> (3,2) and (2,3)
# 4. Frankfurt and Krakow         -> (7,1) and (1,7)
# 5. Naples and Dublin            -> (4,0) and (0,4)
# 6. Krakow and Brussels          -> (1,5) and (5,1)
# 7. Naples and Istanbul          -> (4,2) and (2,4)
# 8. Naples and Brussels          -> (4,5) and (5,4)
# 9. Istanbul and Frankfurt       -> (2,7) and (7,2)
#10. from Brussels to Frankfurt   -> (5,7)   [one-way only]
#11. Istanbul and Krakow          -> (2,1) and (1,2)
#12. Istanbul and Brussels        -> (2,5) and (5,2)
#13. Venice and Frankfurt         -> (3,7) and (7,3)
#14. Naples and Frankfurt         -> (4,7) and (7,4)
#15. Dublin and Krakow            -> (0,1) and (1,0)
#16. Venice and Brussels          -> (3,5) and (5,3)
#17. Naples and Venice            -> (4,3) and (3,4)
#18. Istanbul and Dublin          -> (2,0) and (0,2)
#19. Venice and Dublin            -> (3,0) and (0,3)
#20. Dublin and Frankfurt         -> (0,7) and (7,0)
# -----------------------------------------------------------------------------

allowed_flights = {
    (0,5), (5,0),
    (6,4), (4,6),
    (3,2), (2,3),
    (7,1), (1,7),
    (4,0), (0,4),
    (1,5), (5,1),
    (4,2), (2,4),
    (4,5), (5,4),
    (2,7), (7,2),
    (5,7),              # from Brussels to Frankfurt (one-way)
    (2,1), (1,2),
    (2,5), (5,2),
    (3,7), (7,3),
    (4,7), (7,4),
    (0,1), (1,0),
    (3,5), (5,3),
    (4,3), (3,4),
    (2,0), (0,2),
    (3,0), (0,3),
    (0,7), (7,0)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We encode an itinerary as an ordering (permutation) of the 8 cities:
#   pos[i] : the index of the city visited at itinerary position i, for i=0,...,7.
#   S[i]   : the arrival (start) day for the city visited at position i.
#
# Constraints:
#   - S[0] = 1.
#   - For the first city (i==0): effective stay = full planned duration.
#   - For each subsequent city (i >= 1): effective stay = (planned duration - 1).
#   - The departure day from the last city must equal day 21.
#
# For city at position i:
#   if i == 0: departure = S[0] + durations[city] - 1.
#   if i > 0:  departure = S[i] + (durations[city] - 1) - 1.
# -----------------------------------------------------------------------------

n = 8
s = Solver()

# Itinerary: a permutation of 0 .. n-1.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival day vector.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#   S[1] = S[0] + (full planned duration of city at pos[0])
# For positions i >= 2:
#   S[i] = S[i-1] + (duration of city at pos[i-1] - 1)
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
        /* pos[i-1]==7 */ durations[7] - 1)))))))
    )

# Trip end constraint:
# For the last city, effective stay is (duration - 1) as it is not the first city.
# Therefore, departure day = S_days[n-1] + (durations - 1) - 1 must equal 21.
last_eff = If(pos[n-1] == 0, durations[0] - 1,
           If(pos[n-1] == 1, durations[1] - 1,
           If(pos[n-1] == 2, durations[2] - 1,
           If(pos[n-1] == 3, durations[3] - 1,
           If(pos[n-1] == 4, durations[4] - 1,
           If(pos[n-1] == 5, durations[5] - 1,
           If(pos[n-1] == 6, durations[6] - 1,
           durations[7] - 1))))))

s.add(S_days[n-1] + last_eff - 1 == 21)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair in the itinerary, there must be a direct flight.
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
# For each city with an event, if that city is visited at itinerary position i,
# then the visit interval (from arrival to departure) must overlap the event window.
#
# For the first city (i == 0):
#   interval = [S, S + durations[city] - 1]
# For subsequent cities (i >= 1):
#   interval = [S, S + (durations[city] - 1) - 1] = [S, S + durations[city] - 2]
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
        # Compute effective stay:
        # - For the first city, effective stay = full duration.
        # - For subsequent cities, effective stay = (duration - 1).
        effective = durations[city_index] if i == 0 else durations[city_index] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")