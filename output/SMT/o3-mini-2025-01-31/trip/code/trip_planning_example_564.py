from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 5 cities:
# 0: Istanbul   – 2 days.
#               Event: Visit relatives in Istanbul between day 6 and 7.
# 1: Rome       – 3 days.
# 2: Seville    – 4 days.
# 3: Naples     – 7 days.
# 4: Santorini  – 4 days.
#               Event: Attend a wedding in Santorini between day 13 and 16.
#
# Total planned days = 2 + 3 + 4 + 7 + 4 = 20.
# There are 4 flight transitions, so the effective trip duration = 20 - 4 = 16 days.
#
# Notes:
# - The trip starts on day 1.
# - In the first city you get the full planned duration.
# - In every subsequent city one day is “lost” due to the direct flight.
# -----------------------------------------------------------------------------
cities    = ["Istanbul", "Rome", "Seville", "Naples", "Santorini"]
durations = [2,          3,      4,        7,       4]

# Event windows: mapping city index to (event_start, event_end)
events = {
    0: (6, 7),    # In Istanbul, visit relatives between day 6 and 7.
    4: (13, 16)   # In Santorini, attend a wedding between day 13 and 16.
}

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# The allowed flights (assumed bidirectional unless otherwise specified) are:
#
# 1. Rome and Santorini       -> (1,4) and (4,1)
# 2. Seville and Rome         -> (2,1) and (1,2)
# 3. Istanbul and Naples      -> (0,3) and (3,0)
# 4. Naples and Santorini     -> (3,4) and (4,3)
# 5. Rome and Naples          -> (1,3) and (3,1)
# 6. Rome and Istanbul        -> (1,0) and (0,1)
# -----------------------------------------------------------------------------
allowed_flights = {
    (1,4), (4,1),
    (2,1), (1,2),
    (0,3), (3,0),
    (3,4), (4,3),
    (1,3), (3,1),
    (1,0), (0,1)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as an ordering (a permutation) of the 5 cities:
#   pos[i] : the index (0 .. 4) of the city visited at itinerary position i.
#   S[i]   : the arrival day at the city visited at position i.
#
# For a visited city:
#   - If it is the first city (i == 0), the visit interval is [S, S + duration - 1].
#   - If it is not the first city (i >= 1), the effective stay is (duration - 1) days,
#         so the visit interval is [S, S + (duration - 1) - 1] = [S, S + duration - 2].
#
# The departure day from the final city must equal day 16.
# -----------------------------------------------------------------------------
n = 5
total_trip = 16
s = Solver()

# Itinerary: permutation over cities 0..4
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector: S[0] ... S[4]
s.add(S_days0 := (IntVector("S", n))[0] == 1)  # start on day 1
S_days = IntVector("S", n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For the first city (position 0):
#   S[1] = S[0] + (full duration of city at pos[0]).
# For each subsequent city (i >= 2):
#   S[i] = S[i-1] + (duration at pos[i-1] - 1)
# -----------------------------------------------------------------------------
# Constraint for position 1:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
         durations[3] if pos[0] == 3 else durations[4])))
)

# For positions 2 to 4:
for i in range(2, n):
    s.add(
        S_days[i] ==
        S_days[i-1] +
        If(pos[i-1] == 0, durations[0] - 1,
        If(pos[i-1] == 1, durations[1] - 1,
        If(pos[i-1] == 2, durations[2] - 1,
        If(pos[i-1] == 3, durations[3] - 1,
             durations[4] - 1)))
    )

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the final city (position n-1), the departure day is defined as:
#   If non-first: S + (duration - 1) - 1 = S + duration - 2.
#
# This value must equal total_trip (16).
# -----------------------------------------------------------------------------
last_effective = If(pos[n-1] == 0, durations[0] - 1,
                   If(pos[n-1] == 1, durations[1] - 1,
                   If(pos[n-1] == 2, durations[2] - 1,
                   If(pos[n-1] == 3, durations[3] - 1,
                        durations[4] - 1))))
s.add(S_days[n-1] + last_effective - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair (pos[i] to pos[i+1]) in the itinerary,
# there must be a direct flight.
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
# For cities with events, if a city is visited at itinerary position i,
# then its visit interval must overlap with the event window.
#
# Visit interval:
#  - If i == 0: [S, S + duration - 1]
#  - If i >= 1: [S, S + duration - 2]
# -----------------------------------------------------------------------------
for i in range(n):
    for city, (ev_start, ev_end) in events.items():
        s.add(
            If(pos[i] == city,
               And(
                   # The visit must start no later than the event end.
                   S_days[i] <= ev_end,
                   # And finish no earlier than the event start.
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
        if i == 0:
            effective = durations[city_index]
        else:
            effective = durations[city_index] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")