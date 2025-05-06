from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 5 cities:
# 0: Prague    – 4 days.
# 1: Stuttgart – 2 days.
#              Event: Wedding in Stuttgart between day 2 and day 3.
# 2: Split     – 2 days.
#              Event: Meet friends in Split between day 3 and day 4.
# 3: Krakow    – 2 days.
# 4: Florence  – 2 days.
#
# Total planned days = 4 + 2 + 2 + 2 + 2 = 12.
# There are 4 flight transitions, so the effective trip duration = 12 - 4 = 8 days.
#
# Note:
# - The trip starts on day 1 in the first city (full duration is enjoyed).
# - In each subsequent city, one day is "lost" due to the flight, so the effective stay is duration - 1.
# -----------------------------------------------------------------------------
cities    = ["Prague", "Stuttgart", "Split", "Krakow", "Florence"]
durations = [4,        2,          2,       2,       2]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    1: (2, 3),   # Stuttgart: Wedding between day 2 and day 3.
    2: (3, 4)    # Split: Meet friends event between day 3 and day 4.
}

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional):
#
# - Stuttgart and Split     -> (Stuttgart, Split) and (Split, Stuttgart)  -> (1,2) and (2,1)
# - Prague and Florence     -> (Prague, Florence) and (Florence, Prague)  -> (0,4) and (4,0)
# - Krakow and Stuttgart    -> (Krakow, Stuttgart) and (Stuttgart, Krakow)  -> (3,1) and (1,3)
# - Krakow and Split        -> (Krakow, Split) and (Split, Krakow)          -> (3,2) and (2,3)
# - Split and Prague        -> (Split, Prague) and (Prague, Split)          -> (2,0) and (0,2)
# - Krakow and Prague       -> (Krakow, Prague) and (Prague, Krakow)        -> (3,0) and (0,3)
# -----------------------------------------------------------------------------
allowed_flights = {
    (1,2), (2,1),
    (0,4), (4,0),
    (3,1), (1,3),
    (3,2), (2,3),
    (2,0), (0,2),
    (3,0), (0,3)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation (ordering) of the 5 cities:
#  pos[i]: index of the city visited at itinerary position i (i = 0,...,4).
#  S[i]: arrival day at the city at position i.
#
# For the first city (i == 0) the visit interval is [S, S + duration - 1].
# For every subsequent city (i >= 1) the effective visit interval is [S, S + duration - 2]
# (one day is lost due to taking the flight).
#
# The departure day from the final city must equal total_trip (8 days).
# -----------------------------------------------------------------------------
n = 5
total_trip = 8
s = Solver()

# Itinerary permutation.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(pos[i] >= 0, pos[i] < n)

# Arrival days.
S = IntVector("S", n)
s.add(S[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#   S[1] = S[0] + full duration of city at pos[0]
#
# For positions i >= 2:
#   S[i] = S[i-1] + (duration of city at pos[i-1] - 1)
# -----------------------------------------------------------------------------
# For position 1:
s.add(
    S[1] == S[0] +
         If(pos[0] == 0, durations[0],
         If(pos[0] == 1, durations[1],
         If(pos[0] == 2, durations[2],
         If(pos[0] == 3, durations[3],
            durations[4]))))
)

# For positions 2 to n-1:
for i in range(2, n):
    s.add(
        S[i] == S[i-1] +
         If(pos[i-1] == 0, durations[0] - 1,
         If(pos[i-1] == 1, durations[1] - 1,
         If(pos[i-1] == 2, durations[2] - 1,
         If(pos[i-1] == 3, durations[3] - 1,
            durations[4] - 1))))
    )

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the final city (position n-1):
#   If the city is not the first city, its effective departure day is:
#       Departure = S[n-1] + (duration - 1) - 1 = S[n-1] + duration - 2.
# This departure must equal total_trip.
# -----------------------------------------------------------------------------
s.add(
    S[n-1] +
    If(pos[n-1] == 0, durations[0] - 1,
    If(pos[n-1] == 1, durations[1] - 1,
    If(pos[n-1] == 2, durations[2] - 1,
    If(pos[n-1] == 3, durations[3] - 1,
         durations[4] - 1)))) - 1
    == total_trip
)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair in the itinerary (i and i+1), there must be a direct flight.
# -----------------------------------------------------------------------------
for i in range(n - 1):
    flights = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                flights.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(flights))

# -----------------------------------------------------------------------------
# Event constraints:
#
# For each event city visited at itinerary position i, the visit interval must
# cover the event window.
#
# The visit interval for a city at position i is:
#   - if i == 0 (first city): [S[i], S[i] + duration - 1]
#   - if i >= 1: [S[i], S[i] + (duration - 1) - 1] = [S[i], S[i] + duration - 2]
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
        city_idx = itinerary[i]
        city_name = cities[city_idx]
        if i == 0:
            departure = arrivals[i] + durations[city_idx] - 1
        else:
            departure = arrivals[i] + durations[city_idx] - 2
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