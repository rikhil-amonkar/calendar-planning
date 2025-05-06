from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 5 cities:
# 0: Dubrovnik – 5 days.
# 1: Warsaw    – 2 days.
# 2: Stuttgart – 7 days.
#               Event: Conference in Stuttgart between day 7 and day 13.
# 3: Bucharest – 6 days.
#               Event: Wedding in Bucharest between day 1 and day 6.
# 4: Copenhagen– 3 days.
#
# Total planned days = 5 + 2 + 7 + 6 + 3 = 23.
# There are 4 flight transitions, so effective trip duration = 23 - 4 = 19 days.
#
# Notes:
# - The trip starts on day 1.
# - In the first city you use its full planned duration.
# - In every subsequent city, one day is “lost” due to the flight.
# -----------------------------------------------------------------------------

cities    = ["Dubrovnik", "Warsaw", "Stuttgart", "Bucharest", "Copenhagen"]
durations = [5,           2,        7,          6,          3]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    2: (7, 13),   # Stuttgart: Conference between day 7 and day 13.
    3: (1, 6)     # Bucharest: Wedding between day 1 and day 6.
}

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# Provided flights (bidirectional):
#
# - Warsaw and Copenhagen   -> (1,4) and (4,1)
# - Stuttgart and Copenhagen-> (2,4) and (4,2)
# - Warsaw and Stuttgart    -> (1,2) and (2,1)
# - Bucharest and Copenhagen-> (3,4) and (4,3)
# - Bucharest and Warsaw    -> (3,1) and (1,3)
# - Copenhagen and Dubrovnik-> (4,0) and (0,4)
# -----------------------------------------------------------------------------
allowed_flights = {
    (1,4), (4,1),
    (2,4), (4,2),
    (1,2), (2,1),
    (3,4), (4,3),
    (3,1), (1,3),
    (4,0), (0,4)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We model an itinerary as an ordering (permutation) of the 5 cities:
#   pos[i] : index of the city visited at itinerary position i, for i=0,...,4.
#   S[i]   : arrival (start) day for the city at itinerary position i.
#
# For a city at position i:
#   If i == 0: departure = S[i] + durations[city] - 1.
#   If i >  0: departure = S[i] + (durations[city] - 1) - 1.
#
# The departure day of the final city must equal day 19.
# -----------------------------------------------------------------------------
n = 5
s = Solver()

# Itinerary permutation.
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

# Constraint for position 1:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    /* pos[0]==4 */ durations[4])))
)

# Constraints for positions 2 to n-1.
for i in range(2, n):
    s.add(
        S_days[i] ==
        S_days[i-1] +
        If(pos[i-1] == 0, durations[0] - 1,
        If(pos[i-1] == 1, durations[1] - 1,
        If(pos[i-1] == 2, durations[2] - 1,
        If(pos[i-1] == 3, durations[3] - 1,
        /* pos[i-1]==4 */ durations[4] - 1)))
    )

# Trip end constraint:
# For the last city, effective stay = (duration - 1), so departure = S_days[n-1] + (duration - 1) - 1 must equal 19.
last_effective = If(pos[n-1] == 0, durations[0] - 1,
                If(pos[n-1] == 1, durations[1] - 1,
                If(pos[n-1] == 2, durations[2] - 1,
                If(pos[n-1] == 3, durations[3] - 1,
                durations[4] - 1))))
s.add(S_days[n-1] + last_effective - 1 == 19)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair in the itinerary, there must be a direct flight.
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
# For each event in a city, if that city appears at itinerary position i,
# then its visit interval must overlap with the event window.
#
# For the first city (i == 0): interval = [S, S + durations[city] - 1].
# For subsequent cities (i > 0): interval = [S, S + (durations[city] - 1) - 1]
# i.e., [S, S + durations[city] - 2].
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
        # Effective stay: full planned duration if first city, otherwise (planned duration - 1)
        effective = durations[city_index] if i == 0 else durations[city_index] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")