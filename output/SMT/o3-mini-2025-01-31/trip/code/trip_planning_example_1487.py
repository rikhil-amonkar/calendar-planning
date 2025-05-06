from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions (index: city, planned duration, event window if any):
#
# 0: Copenhagen – Planned stay: 5 days.
#       Event: Meet a friend between day 11 and day 15.
# 1: Geneva     – Planned stay: 3 days.
# 2: Mykonos    – Planned stay: 2 days.
#       Event: Attend a conference between day 27 and day 28.
# 3: Naples     – Planned stay: 4 days.
#       Event: Visit relatives between day 5 and day 8.
# 4: Prague     – Planned stay: 2 days.
# 5: Dubrovnik  – Planned stay: 3 days.
# 6: Athens     – Planned stay: 4 days.
#       Event: Attend a workshop between day 8 and day 11.
# 7: Santorini  – Planned stay: 5 days.
# 8: Brussels   – Planned stay: 4 days.
# 9: Munich     – Planned stay: 5 days.
#
# Total planned days = 5+3+2+4+2+3+4+5+4+5 = 37.
# There will be 9 flight days.
# Thus effective trip duration = 37 - 9 = 28 days.
#
# Note: Our scheduling model is as in previous examples:
#   - The trip starts on day 1.
#   - The visit to the first city is for its full planned duration.
#   - Every subsequent city’s visit is reduced by one day (since one day is used for the flight).
#   - Therefore, if city X is visited in a non-first position the "effective duration" is (planned duration - 1).
#
# For a city visited at itinerary position i, if we denote its arrival day as S[i],
# then its visit interval is: [S[i], S[i] + effective - 1].
#
# The trip end constraint is:
#     S[last] + (effective duration for the last city) - 1 == 28.
# -----------------------------------------------------------------------------

cities    = ["Copenhagen", "Geneva", "Mykonos", "Naples", "Prague", 
             "Dubrovnik", "Athens", "Santorini", "Brussels", "Munich"]
durations = [5, 3, 2, 4, 2, 3, 4, 5, 4, 5]

# Event windows: dictionary mapping city index to (event_start, event_end)
# The constraint will require that the visit interval (which may be shortened) 
# overlaps the event window.
events = {
    0: (11, 15),  # Copenhagen: friend meeting between day 11 and 15.
    2: (27, 28),  # Mykonos: conference between day 27 and 28.
    3: (5, 8),    # Naples: relatives visit between day 5 and 8.
    6: (8, 11)    # Athens: workshop between day 8 and 11.
}

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional) as given:
#
# "Copenhagen and Dubrovnik" -> (0,5) and (5,0)
# "Brussels and Copenhagen"   -> (8,0) and (0,8)
# "Prague and Geneva"         -> (4,1) and (1,4)
# "Athens and Geneva"         -> (6,1) and (1,6)
# "Naples and Dubrovnik"      -> (3,5) and (5,3)
# "Athens and Dubrovnik"      -> (6,5) and (5,6)
# "Geneva and Mykonos"        -> (1,2) and (2,1)
# "Naples and Mykonos"        -> (3,2) and (2,3)
# "Naples and Copenhagen"     -> (3,0) and (0,3)
# "Munich and Mykonos"        -> (9,2) and (2,9)
# "Naples and Athens"         -> (3,6) and (6,3)
# "Prague and Athens"         -> (4,6) and (6,4)
# "Santorini and Geneva"      -> (7,1) and (1,7)
# "Athens and Santorini"      -> (6,7) and (7,6)
# "Naples and Munich"         -> (3,9) and (9,3)
# "Prague and Copenhagen"     -> (4,0) and (0,4)
# "Brussels and Naples"       -> (8,3) and (3,8)
# "Athens and Mykonos"        -> (6,2) and (2,6)
# "Athens and Copenhagen"     -> (6,0) and (0,6)
# "Naples and Geneva"         -> (3,1) and (1,3)
# "Dubrovnik and Munich"      -> (5,9) and (9,5)
# "Brussels and Munich"       -> (8,9) and (9,8)
# "Prague and Brussels"       -> (4,8) and (8,4)
# "Brussels and Athens"       -> (8,6) and (6,8)
# "Athens and Munich"         -> (6,9) and (9,6)
# "Geneva and Munich"         -> (1,9) and (9,1)
# "Copenhagen and Munich"     -> (0,9) and (9,0)
# "Brussels and Geneva"       -> (8,1) and (1,8)
# "Copenhagen and Geneva"     -> (0,1) and (1,0)
# "Prague and Munich"         -> (4,9) and (9,4)
# "Copenhagen and Santorini"  -> (0,7) and (7,0)
# "Naples and Santorini"      -> (3,7) and (7,3)
# "Geneva and Dubrovnik"      -> (1,5) and (5,1)
# -----------------------------------------------------------------------------

allowed_flights = {
    (0,5), (5,0),
    (8,0), (0,8),
    (4,1), (1,4),
    (6,1), (1,6),
    (3,5), (5,3),
    (6,5), (5,6),
    (1,2), (2,1),
    (3,2), (2,3),
    (3,0), (0,3),
    (9,2), (2,9),
    (3,6), (6,3),
    (4,6), (6,4),
    (7,1), (1,7),
    (6,7), (7,6),
    (3,9), (9,3),
    (4,0), (0,4),
    (8,3), (3,8),
    (6,2), (2,6),
    (6,0), (0,6),
    (3,1), (1,3),
    (5,9), (9,5),
    (8,9), (9,8),
    (4,8), (8,4),
    (8,6), (6,8),
    (6,9), (9,6),
    (1,9), (9,1),
    (0,9), (9,0),
    (8,1), (1,8),
    (0,1), (1,0),
    (4,9), (9,4),
    (0,7), (7,0),
    (3,7), (7,3),
    (1,5), (5,1)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We have 10 cities, and we assume the trip itinerary is a permutation of them.
# Let pos[i] be the index (0..9) of the city visited at the i-th position.
#
# Let S[i] be the arrival day at the city in position i.
#
# The trip starts on day 1, so S[0] == 1.
#
# The effective stay for the city at position i is defined as:
#    effective = durations[city]      if i == 0 (first city)
#    effective = durations[city] - 1  if i >= 1
#
# And the trip end constraint is:
#    S[9] + effective(last city) - 1 == 28.
# -----------------------------------------------------------------------------

n = 10
s = Solver()

# Itinerary: permutation of 0..9
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector
S_days = IntVector("S", n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints.
#
# For the first city, arrival day is fixed to 1.
# For the 2nd city (i=1):
#    S[1] = S[0] + (full planned duration for city at pos[0])
#
# For subsequent cities i>=2:
#    S[i] = S[i-1] + ((planned duration for city at pos[i-1]) - 1)
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
    /* else: pos[0]==9 */ durations[9])))))))))
)

# For positions 2 to 9:
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
        /* else: pos[i-1]==9 */ durations[9] - 1))))))))        
    )

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# Let last_eff = durations[city] if the city at pos[n-1] is in position 0 (only city),
# else last_eff = durations[city] - 1.
# Then we require: S_days[n-1] + last_eff - 1 == 28.
# -----------------------------------------------------------------------------
last_eff = If(n == 1,
              If(pos[n-1] == 0, durations[0],
              If(pos[n-1] == 1, durations[1],
              If(pos[n-1] == 2, durations[2],
              If(pos[n-1] == 3, durations[3],
              If(pos[n-1] == 4, durations[4],
              If(pos[n-1] == 5, durations[5],
              If(pos[n-1] == 6, durations[6],
              If(pos[n-1] == 7, durations[7],
              If(pos[n-1] == 8, durations[8],
              durations[9]))))))))),
              If(pos[n-1] == 0, durations[0] - 1,
              If(pos[n-1] == 1, durations[1] - 1,
              If(pos[n-1] == 2, durations[2] - 1,
              If(pos[n-1] == 3, durations[3] - 1,
              If(pos[n-1] == 4, durations[4] - 1,
              If(pos[n-1] == 5, durations[5] - 1,
              If(pos[n-1] == 6, durations[6] - 1,
              If(pos[n-1] == 7, durations[7] - 1,
              If(pos[n-1] == 8, durations[8] - 1,
              durations[9] - 1)))))))))
s.add(S_days[n-1] + last_eff - 1 == 28)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair of visited cities (pos[i], pos[i+1]),
# there must be a direct flight according to allowed_flights.
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
# For each city with an event (according to the events dict), if that city is visited
# at itinerary position i then let effective = (durations[city] if i == 0 else durations[city] - 1),
# and require that the visit interval [S_days[i], S_days[i] + effective - 1] overlaps the event window.
#
# Specifically, if the event window is [E_start, E_end] then we require:
#      S_days[i] <= E_end  and  S_days[i] + effective - 1 >= E_start.
# -----------------------------------------------------------------------------
for i in range(n):
    for city, (e_start, e_end) in events.items():
        s.add(
            If(pos[i] == city,
               And(
                   S_days[i] <= e_end,
                   If(i == 0,
                      S_days[i] + durations[city] - 1 >= e_start,
                      S_days[i] + (durations[city] - 1) - 1 >= e_start)
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
        city = cities[itinerary[i]]
        effective = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1:2d}: {city:12s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] +
                          (durations[itinerary[n-1]] if n==1 else durations[itinerary[n-1]] - 1) - 1)
    print(f"Trip ends on day: {trip_end}")
else:
    print("No valid trip plan could be found.")