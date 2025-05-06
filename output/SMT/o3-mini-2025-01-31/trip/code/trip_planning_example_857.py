from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 7 cities:
# 0: Porto      – 2 days.
# 1: Geneva     – 3 days.
# 2: Mykonos    – 3 days.
#      Event: Meet a friend in Mykonos between day 10 and day 12.
# 3: Manchester – 4 days.
#      Event: Wedding in Manchester between day 15 and day 18.
# 4: Hamburg    – 5 days.
# 5: Naples     – 5 days.
# 6: Frankfurt  – 2 days.
#      Event: Annual show in Frankfurt from day 5 to day 6.
#
# Total planned days = 2 + 3 + 3 + 4 + 5 + 5 + 2 = 24.
# There are 6 flight transitions, so the effective trip duration = 24 - 6 = 18 days.
#
# Notes:
# - The trip starts on day 1.
# - In the first city you get to use the full planned duration.
# - In every subsequent city one day is “lost” due to the flight (effective stay = planned duration - 1).
# -----------------------------------------------------------------------------

cities    = ["Porto", "Geneva", "Mykonos", "Manchester", "Hamburg", "Naples", "Frankfurt"]
durations = [2,       3,        3,         4,           5,         5,       2]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    2: (10, 12),  # Mykonos: meet a friend between day 10 and 12.
    3: (15, 18),  # Manchester: wedding between day 15 and 18.
    6: (5, 6)     # Frankfurt: annual show between day 5 and 6.
}

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# Provided pairs (bidirectional unless noted otherwise):
#
# 1. Hamburg and Frankfurt   -> (4,6) and (6,4)
# 2. Naples and Mykonos      -> (5,2) and (2,5)
# 3. Hamburg and Porto       -> (4,0) and (0,4)
# 4. from Hamburg to Geneva   -> (4,1) [one-way only]
# 5. Mykonos and Geneva       -> (2,1) and (1,2)
# 6. Frankfurt and Geneva     -> (6,1) and (1,6)
# 7. Frankfurt and Porto      -> (6,0) and (0,6)
# 8. Geneva and Porto         -> (1,0) and (0,1)
# 9. Geneva and Manchester    -> (1,3) and (3,1)
#10. Naples and Manchester    -> (5,3) and (3,5)
#11. Frankfurt and Naples     -> (6,5) and (5,6)
#12. Frankfurt and Manchester -> (6,3) and (3,6)
#13. Naples and Geneva        -> (5,1) and (1,5)
#14. Porto and Manchester     -> (0,3) and (3,0)
#15. Hamburg and Manchester   -> (4,3) and (3,4)
# -----------------------------------------------------------------------------

allowed_flights = {
    (4,6), (6,4),
    (5,2), (2,5),
    (4,0), (0,4),
    (4,1),              # one-way from Hamburg to Geneva only
    (2,1), (1,2),
    (6,1), (1,6),
    (6,0), (0,6),
    (1,0), (0,1),
    (1,3), (3,1),
    (5,3), (3,5),
    (6,5), (5,6),
    (6,3), (3,6),
    (5,1), (1,5),
    (0,3), (3,0),
    (4,3), (3,4)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We model an itinerary as a permutation of the 7 cities:
#   pos[i] : the index of the city visited at itinerary position i (i=0,...,6)
#   S[i]   : the arrival day for the city at itinerary position i.
#
# Constraints:
#   - S[0] = 1.
#   - For the first city, effective stay = full planned duration.
#   - For every subsequent city, effective stay = (planned duration - 1).
#   - The departure day of the last city must equal day 18.
#
# The departure day is computed as:
#   if i == 0: departure = S[i] + durations[city] - 1.
#   if i > 0:  departure = S[i] + (durations[city] - 1) - 1.
# -----------------------------------------------------------------------------

n = 7
s = Solver()

# Itinerary: permutation of cities
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)  # Trip starts on day 1.
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

# Position 1:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    If(pos[0] == 4, durations[4],
    If(pos[0] == 5, durations[5],
    /* pos[0]==6 */ durations[6])))))
)

# Positions 2 to n-1:
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
        /* pos[i-1]==6 */ durations[6] - 1)))))
    )

# Trip end constraint:
# For the last city, effective stay = duration - 1, so
# departure = S[n-1] + (durations - 1) - 1 = S[n-1] + durations - 2 must equal 18.
last_eff = If(pos[n-1] == 0, durations[0] - 1,
           If(pos[n-1] == 1, durations[1] - 1,
           If(pos[n-1] == 2, durations[2] - 1,
           If(pos[n-1] == 3, durations[3] - 1,
           If(pos[n-1] == 4, durations[4] - 1,
           If(pos[n-1] == 5, durations[5] - 1,
           durations[6] - 1)))))
s.add(S_days[n-1] + last_eff - 1 == 18)

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
# For a city with an event, if the city is visited at itinerary position i, then its visitation
# interval (from arrival to departure) must overlap with the event window.
#
# For the first city (i == 0): interval = [S, S + durations[city] - 1]
# For subsequent cities (i >= 1): interval = [S, S + (durations[city] - 1) - 1] 
#                                  i.e., [S, S + durations[city] - 2]
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
        # Calculate effective stay: full duration if first, otherwise (duration - 1)
        effective = durations[city_index] if i == 0 else durations[city_index] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")