from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions:
#
# We have 6 cities:
# 0: Amsterdam – Planned stay: 4 days.
#       Event: Visit relatives in Amsterdam between day 5 and day 8.
# 1: Edinburgh – Planned stay: 5 days.
# 2: Brussels  – Planned stay: 5 days.
# 3: Vienna    – Planned stay: 5 days.
# 4: Berlin    – Planned stay: 4 days.
#       Event: Meet a friend in Berlin between day 16 and day 19.
# 5: Reykjavik – Planned stay: 5 days.
#       Event: Workshop in Reykjavik between day 12 and day 16.
#
# Total planned days = 4 + 5 + 5 + 5 + 4 + 5 = 28.
# There will be 5 flight days (one for each transition).
# Thus effective trip duration = 28 - 5 = 23 days.
#
# Note: The trip starts on day 1.
# For the first visited city, the effective stay is the full planned duration.
# For subsequent cities, we subtract one day for the flight, thus effective = (planned duration - 1).
#
# For a city visited at itinerary position i, if S[i] is the arrival day then the visit interval is:
#    [S[i], S[i] + effective - 1]
# and we require that the trip end day (last arrival + effective - 1) equals 23.
# -----------------------------------------------------------------------------

cities    = ["Amsterdam", "Edinburgh", "Brussels", "Vienna", "Berlin", "Reykjavik"]
durations = [4, 5, 5, 5, 4, 5]

# Event windows: mapping city index -> (event start, event end)
# Amsterdam relatives: between day 5 and day 8.
# Berlin friend meeting: between day 16 and day 19.
# Reykjavik workshop: between day 12 and day 16.
events = {
    0: (5, 8),
    4: (16, 19),
    5: (12, 16)
}

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional):
#
# "Edinburgh and Berlin"      -> (1,4) and (4,1)
# "Amsterdam and Berlin"      -> (0,4) and (4,0)
# "Edinburgh and Amsterdam"   -> (1,0) and (0,1)
# "Vienna and Berlin"         -> (3,4) and (4,3)
# "Berlin and Brussels"       -> (4,2) and (2,4)
# "Vienna and Reykjavik"      -> (3,5) and (5,3)
# "Edinburgh and Brussels"    -> (1,2) and (2,1)
# "Vienna and Brussels"       -> (3,2) and (2,3)
# "Amsterdam and Reykjavik"   -> (0,5) and (5,0)
# "Reykjavik and Brussels"    -> (5,2) and (2,5)
# "Amsterdam and Vienna"      -> (0,3) and (3,0)
# "Reykjavik and Berlin"      -> (5,4) and (4,5)
# -----------------------------------------------------------------------------

allowed_flights = {
    (1,4), (4,1),
    (0,4), (4,0),
    (1,0), (0,1),
    (3,4), (4,3),
    (4,2), (2,4),
    (3,5), (5,3),
    (1,2), (2,1),
    (3,2), (2,3),
    (0,5), (5,0),
    (5,2), (2,5),
    (0,3), (3,0),
    (5,4), (4,5)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We assume the itinerary is a permutation of the 6 cities.
# pos[i] denotes the index of the city visited at position i.
#
# S[i] denotes the arrival day at the city in position i.
#
# Constraint:
# - S[0] == 1 (trip starts on day 1).
# - For position 1: S[1] = S[0] + (duration of city at pos[0]).
# - For positions i>=2: S[i] = S[i-1] + (duration of city at pos[i-1] - 1).
# - Trip end: S[5] + (effective stay for city at pos[5]) - 1 = 23.
# -----------------------------------------------------------------------------

n = 6
s = Solver()

# Itinerary: permutation of 0..5
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days:
S_days = IntVector("S", n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#   S[1] = S[0] + (full planned duration of city at pos[0])
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    /* else: pos[0]==4 or pos[0]==5 */
         If(pos[0] == 4, durations[4], durations[5]))))
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
        If(pos[i-1] == 4, durations[4] - 1, durations[5] - 1)))))
    )

# Trip end constraint:
# effective stay for last city (position n-1) = durations[city] - 1 (since it's not the first city)
last_eff = If(pos[n-1] == 0, durations[0] - 1,
            If(pos[n-1] == 1, durations[1] - 1,
            If(pos[n-1] == 2, durations[2] - 1,
            If(pos[n-1] == 3, durations[3] - 1,
            If(pos[n-1] == 4, durations[4] - 1, durations[5] - 1)))))
s.add(S_days[n-1] + last_eff - 1 == 23)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair (pos[i], pos[i+1]), a direct flight must exist.
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
# For each event in a city, if that city is visited at itinerary
# position i, then let effective = durations[city] if i==0, else (durations[city]-1),
# and the visit interval is [S_days[i], S_days[i] + effective - 1].
# We require that the event window [event_start, event_end] overlaps the visit interval:
#   S_days[i] <= event_end  AND  (S_days[i] + effective - 1) >= event_start
# -----------------------------------------------------------------------------
for i in range(n):
    for city, (event_start, event_end) in events.items():
        s.add(
            If(pos[i] == city,
               And(
                   S_days[i] <= event_end,
                   If(i == 0,
                      S_days[i] + durations[city] - 1 >= event_start,
                      S_days[i] + (durations[city] - 1) - 1 >= event_start)
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
        city_name = cities[itinerary[i]]
        effective = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] +
                          (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")