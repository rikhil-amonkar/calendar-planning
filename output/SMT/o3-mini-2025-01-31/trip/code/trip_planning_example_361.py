from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 4 cities:
# 0: Paris     – 6 days.
# 1: Madrid    – 7 days.
#              Event: Annual show in Madrid from day 1 to day 7.
# 2: Bucharest – 2 days.
#              Event: Visit relatives in Bucharest between day 14 and day 15.
# 3: Seville   – 3 days.
#
# Total planned days = 6 + 7 + 2 + 3 = 18.
# There are 3 transitions (flights), so effective trip duration = 18 - 3 = 15 days.
#
# Notes:
# - The trip starts on day 1.
# - In the very first city, you use its full planned duration.
# - In every subsequent city, one day is "lost" due to flying (so effective stay = planned duration - 1).
# -----------------------------------------------------------------------------

cities    = ["Paris", "Madrid", "Bucharest", "Seville"]
durations = [6,       7,       2,         3]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    1: (1, 7),    # Madrid: Annual show from day 1 to day 7.
    2: (14, 15)   # Bucharest: Visit relatives between day 14 and 15.
}

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# Provided flights (bidirectional unless specified otherwise):
#
# - Paris and Bucharest        -> (0,2) and (2,0)
# - Seville and Paris          -> (3,0) and (0,3)
# - Madrid and Bucharest       -> (1,2) and (2,1)
# - Madrid and Paris           -> (1,0) and (0,1)
# - Madrid and Seville         -> (1,3) and (3,1)
# -----------------------------------------------------------------------------

allowed_flights = {
    (0,2), (2,0),
    (3,0), (0,3),
    (1,2), (2,1),
    (1,0), (0,1),
    (1,3), (3,1)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We model an itinerary as an ordering (permutation) of the 4 cities:
#   pos[i] : the index of the city visited at itinerary position i, i = 0,...,3.
#   S[i]   : the arrival (start) day for the city at itinerary position i.
#
# Constraints:
#   - S[0] = 1.
#   - For position 0: effective stay = full planned duration.
#   - For positions >= 1: effective stay = planned duration - 1.
#   - Departure day of the final city must equal day 15.
#
# Departure day is computed as:
#   if i == 0: departure = S[0] + durations[city] - 1.
#   if i >= 1: departure = S[i] + (durations[city] - 1) - 1.
# -----------------------------------------------------------------------------

n = 4
s = Solver()

# Itinerary positions (as permutation of city indices).
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
# For position 1: S[1] = S[0] + (full planned duration of city at pos[0]).
# For positions i >= 2: 
#   S[i] = S[i-1] + (duration of city at pos[i-1] - 1).
# -----------------------------------------------------------------------------

# Position 1:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    /* pos[0]==3 */ durations[3])))
)

# Positions 2 to n-1.
for i in range(2, n):
    s.add(
        S_days[i] ==
        S_days[i-1] +
        If(pos[i-1] == 0, durations[0] - 1,
        If(pos[i-1] == 1, durations[1] - 1,
        If(pos[i-1] == 2, durations[2] - 1,
        /* pos[i-1]==3 */ durations[3] - 1)))
    )

# Trip end constraint:
# For the last city (position n-1), effective stay is (duration - 1) since it's not the first city.
# So its departure day = S_days[n-1] + (duration - 1) - 1 must equal 15.
last_eff = If(pos[n-1] == 0, durations[0] - 1,
           If(pos[n-1] == 1, durations[1] - 1,
           If(pos[n-1] == 2, durations[2] - 1,
           durations[3] - 1)))
s.add(S_days[n-1] + last_eff - 1 == 15)

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
# For each city that has an event, if that city appears at itinerary position i,
# then the visit interval must overlap with the event window.
#
# For the first city (i == 0): interval = [S, S + durations[city] - 1].
# For subsequent cities (i >= 1): interval = [S, S + (durations[city]-1) - 1] i.e., [S, S + durations[city] - 2].
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
        # For the first city: effective stay = full duration; for the rest: duration - 1.
        effective = durations[city_index] if i == 0 else durations[city_index] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")