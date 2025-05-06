from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 4 cities:
# 0: Seville  – 2 days.
# 1: Stuttgart– 7 days.
#              Event: Attend a conference in Stuttgart – your stay must cover some time
#                     during the conference window [7, 13] (i.e. your visit interval 
#                     must intersect this window).
# 2: Porto    – 3 days.
# 3: Madrid   – 4 days.
#              Event: Visit relatives in Madrid between day 1 and day 4.
#
# Total planned days = 2 + 7 + 3 + 4 = 16.
# There are 3 flight transitions, so the effective trip duration = 16 - 3 = 13 days.
#
# Notes:
# - The trip starts on day 1.
# - When you visit the first city you enjoy its full planned duration.
# - In every subsequent city one day is “lost” due to the flight.
#   (Thus, if you visit a city as non-first, you are present only for (duration – 1) days.)
# -----------------------------------------------------------------------------
cities    = ["Seville", "Stuttgart", "Porto", "Madrid"]
durations = [2,         7,          3,      4]

# Event windows (interpreted as intervals that your visit must at least intersect):
# For Stuttgart, your visit must cover some day between 7 and 13.
# For Madrid, your visit must cover some day between 1 and 4.
events = {
    1: (7, 13),  # Stuttgart conference: visit must intersect [7, 13]
    3: (1, 4)    # Madrid relatives: visit must intersect [1, 4]
}

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# The allowed flights between these cities (bidirectional unless noted) are:
#
# - Porto and Stuttgart      -> (2,1) and (1,2)
# - Seville and Porto        -> (0,2) and (2,0)
# - Madrid and Porto         -> (3,2) and (2,3)
# - Madrid and Seville       -> (3,0) and (0,3)
# -----------------------------------------------------------------------------
allowed_flights = {
    (2,1), (1,2),
    (0,2), (2,0),
    (3,2), (2,3),
    (3,0), (0,3)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as an ordering (a permutation) of the 4 cities:
#   pos[i] : the index (0..3) of the city visited at position i, for i=0,...,3.
#   S[i]   : the arrival (start) day at city pos[i].
#
# The departure day from a visited city is computed as follows:
#   - If the city is the first visited (i==0): 
#         departure = S[i] + durations[city] - 1.
#   - Otherwise (i>=1): 
#         departure = S[i] + (durations[city] - 1) - 1.
#
# The departure day from the last city must equal the overall trip day, 13.
# -----------------------------------------------------------------------------
n = 4
total_trip = 13
s = Solver()

# Permutation of cities.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)  # the trip starts on day 1
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For the first city (position 0): 
#   S[1] = S[0] + (full planned duration of the city at pos[0]).
# For every subsequent city (i >= 2):
#   S[i] = S[i-1] + (duration of city at pos[i-1] - 1)
# -----------------------------------------------------------------------------
# Position 1:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    /* pos[0]==3 */ durations[3])))
)

# Positions 2 to n-1:
for i in range(2, n):
    s.add(
        S_days[i] ==
        S_days[i-1] +
        If(pos[i-1] == 0, durations[0] - 1,
        If(pos[i-1] == 1, durations[1] - 1,
        If(pos[i-1] == 2, durations[2] - 1,
        /* pos[i-1]==3 */ durations[3] - 1))
    )
)

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# The departure day from the last city must equal total_trip.
# For non-first cities, effective stay = (duration - 1); thus, departure = S + (duration-1) - 1.
# (Note: Since n >=2 in our case, the last city is always non-first.)
# -----------------------------------------------------------------------------
last_effective = If(pos[n-1] == 0, durations[0] - 1,
                If(pos[n-1] == 1, durations[1] - 1,
                If(pos[n-1] == 2, durations[2] - 1,
                durations[3] - 1)))
s.add(S_days[n-1] + last_effective - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair (pos[i] to pos[i+1]) in the itinerary,
# there must be an allowed direct flight.
# -----------------------------------------------------------------------------
for i in range(n-1):
    flight_options = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                flight_options.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(flight_options))

# -----------------------------------------------------------------------------
# Event constraints:
#
# If a city with an event is visited at itinerary position i,
# then its visit interval must intersect the event window.
#
# The visit interval is defined as:
#   If i == 0: [S[i], S[i] + durations[city] - 1]
#   If i >= 1: [S[i], S[i] + (durations[city] - 1) - 1]
#
# For Stuttgart (city 1), we require the interval to intersect [7, 13].
# For Madrid (city 3), we require the interval to intersect [1, 4].
# -----------------------------------------------------------------------------
for i in range(n):
    for city, (ev_start, ev_end) in events.items():
        s.add(
            If(pos[i] == city,
               And(
                   # The visit must start no later than the event end,
                   # and finish no earlier than the event start.
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
        # Determine effective stay: first city gets full duration; others get (duration - 1)
        if i == 0:
            effective = durations[city_index]
        else:
            effective = durations[city_index] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:9s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")