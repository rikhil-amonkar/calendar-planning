from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions:
#
# We have 8 cities:
# 0: Oslo       – planned stay: 2 days.
#                Event: attend an annual show in Oslo between day 16 and day 17.
# 1: Reykjavik  – planned stay: 5 days.
#                Event: meet a friend in Reykjavik between day 9 and day 13.
# 2: Stockholm  – planned stay: 4 days.
# 3: Munich     – planned stay: 4 days.
#                Event: visit relatives in Munich between day 13 and day 16.
# 4: Frankfurt  – planned stay: 4 days.
#                Event: attend a workshop in Frankfurt between day 17 and day 20.
# 5: Barcelona  – planned stay: 3 days.
# 6: Bucharest  – planned stay: 2 days.
# 7: Split      – planned stay: 3 days.
#
# Total planned days = 2 + 5 + 4 + 4 + 4 + 3 + 2 + 3 = 27.
# There will be 7 flight days (one per transition), so the effective duration is
# 27 – 7 = 20 days.
# -----------------------------------------------------------------------------

cities = ["Oslo", "Reykjavik", "Stockholm", "Munich", "Frankfurt", "Barcelona", "Bucharest", "Split"]
durations = [2, 5, 4, 4, 4, 3, 2, 3]

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# The provided flights between cities are (bidirectional):
#
# Reykjavik and Munich         -> (1,3) and (3,1)
# Munich and Frankfurt         -> (3,4) and (4,3)
# Split and Oslo               -> (7,0) and (0,7)
# Reykjavik and Oslo           -> (1,0) and (0,1)
# Bucharest and Munich         -> (6,3) and (3,6)
# Oslo and Frankfurt           -> (0,4) and (4,0)
# Bucharest and Barcelona      -> (6,5) and (5,6)
# Barcelona and Frankfurt      -> (5,4) and (4,5)
# Reykjavik and Frankfurt      -> (1,4) and (4,1)
# Barcelona and Stockholm      -> (5,2) and (2,5)
# Barcelona and Reykjavik      -> (5,1) and (1,5)
# Stockholm and Reykjavik      -> (2,1) and (1,2)
# Barcelona and Split          -> (5,7) and (7,5)
# Bucharest and Oslo           -> (6,0) and (0,6)
# Bucharest and Frankfurt      -> (6,4) and (4,6)
# Split and Stockholm          -> (7,2) and (2,7)
# Barcelona and Oslo           -> (5,0) and (0,5)
# Stockholm and Munich         -> (2,3) and (3,2)
# Stockholm and Oslo           -> (2,0) and (0,2)
# Split and Frankfurt          -> (7,4) and (4,7)
# Barcelona and Munich         -> (5,3) and (3,5)
# Stockholm and Frankfurt      -> (2,4) and (4,2)
# Munich and Oslo              -> (3,0) and (0,3)
# Split and Munich             -> (7,3) and (3,7)
# -----------------------------------------------------------------------------

allowed_flights = {
    (1,3), (3,1),
    (3,4), (4,3),
    (7,0), (0,7),
    (1,0), (0,1),
    (6,3), (3,6),
    (0,4), (4,0),
    (6,5), (5,6),
    (5,4), (4,5),
    (1,4), (4,1),
    (5,2), (2,5),
    (5,1), (1,5),
    (2,1), (1,2),
    (5,7), (7,5),
    (6,0), (0,6),
    (6,4), (4,6),
    (7,2), (2,7),
    (5,0), (0,5),
    (2,3), (3,2),
    (2,0), (0,2),
    (7,4), (4,7),
    (5,3), (3,5),
    (2,4), (4,2),
    (3,0), (0,3),
    (7,3), (3,7)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# pos[i]: city at itinerary position i, for i=0,...,7. They form a permutation
#         of {0,...,7}.
#
# S[i]: arrival day at the city visited at position i.
# The trip starts on day 1, so S[0] == 1.
#
# Effective stay:
#   For the first city: full planned duration.
#   For subsequent cities: (planned duration - 1) days.
# -----------------------------------------------------------------------------

n = 8
s = Solver()

# Itinerary: permutation of city indices.
pos = IntVector('pos', n)
s.add(Distinct(pos))
for i in range(n):
    s.add(pos[i] >= 0, pos[i] < n)

# Arrival days for each visited city.
S_days = IntVector('S', n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 0: S[0] = 1.
# For position 1: S[1] = S[0] + (full duration for city at pos[0]).
# For positions i>=2: S[i] = S[i-1] + (planned duration of previous city - 1).
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
    /* else (pos[0]==7): */ durations[7])))))))
)

# For positions 2 to 7:
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
        /* else (pos[i-1]==7): */ durations[7] - 1)))))))
    )

# Trip end constraint:
# Let effective stay for the last city be (full duration if first city, else duration-1)
last_eff = If(n == 1,
              If(pos[n-1] == 0, durations[0],
              If(pos[n-1] == 1, durations[1],
              If(pos[n-1] == 2, durations[2],
              If(pos[n-1] == 3, durations[3],
              If(pos[n-1] == 4, durations[4],
              If(pos[n-1] == 5, durations[5],
              If(pos[n-1] == 6, durations[6],
              durations[7]))))))),
              If(pos[n-1] == 0, durations[0] - 1,
              If(pos[n-1] == 1, durations[1] - 1,
              If(pos[n-1] == 2, durations[2] - 1,
              If(pos[n-1] == 3, durations[3] - 1,
              If(pos[n-1] == 4, durations[4] - 1,
              If(pos[n-1] == 5, durations[5] - 1,
              If(pos[n-1] == 6, durations[6] - 1,
              durations[7] - 1)))))))
s.add(S_days[n-1] + last_eff - 1 == 20)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair (pos[i], pos[i+1]), there must be a direct flight.
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
# (a) Oslo (city 0) event: Annual show from day 16 to day 17.
#     Effective visit interval must overlap [16, 17].
#
# (b) Reykjavik (city 1) event: Meet a friend between day 9 and day 13.
#
# (c) Munich (city 3) event: Visit relatives between day 13 and day 16.
#
# (d) Frankfurt (city 4) event: Attend a workshop between day 17 and day 20.
#
# Note: Effective stay = full duration if city is visited first,
#       else (planned duration - 1).
# -----------------------------------------------------------------------------
for i in range(n):
    # If city is Oslo (0)
    s.add(
        If(pos[i] == 0,
           And(
               S_days[i] <= 17,
               If(i == 0,
                  S_days[i] + durations[0] - 1 >= 16,
                  S_days[i] + (durations[0] - 1) - 1 >= 16)
           ),
           True)
    )
    # If city is Reykjavik (1)
    s.add(
        If(pos[i] == 1,
           And(
               S_days[i] <= 13,
               If(i == 0,
                  S_days[i] + durations[1] - 1 >= 9,
                  S_days[i] + (durations[1] - 1) - 1 >= 9)
           ),
           True)
    )
    # If city is Munich (3)
    s.add(
        If(pos[i] == 3,
           And(
               S_days[i] <= 16,
               If(i == 0,
                  S_days[i] + durations[3] - 1 >= 13,
                  S_days[i] + (durations[3] - 1) - 1 >= 13)
           ),
           True)
    )
    # If city is Frankfurt (4)
    s.add(
        If(pos[i] == 4,
           And(
               S_days[i] <= 20,
               If(i == 0,
                  S_days[i] + durations[4] - 1 >= 17,
                  S_days[i] + (durations[4] - 1) - 1 >= 17)
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
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")

    trip_end = m.evaluate(S_days[n-1] +
                          (durations[itinerary[n-1]] if n == 1 else (durations[itinerary[n-1]] - 1)) - 1)
    print(f"Trip ends on day: {trip_end}")
else:
    print("No valid trip plan could be found.")