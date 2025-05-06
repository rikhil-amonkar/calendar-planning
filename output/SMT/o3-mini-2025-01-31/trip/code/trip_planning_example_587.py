from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions:
#
# We have 5 cities:
# 0: Manchester – Planned stay: 3 days.
#                 Event: Attend a wedding in Manchester between day 1 and day 3.
# 1: Istanbul   – Planned stay: 7 days.
# 2: Venice     – Planned stay: 7 days.
#                 Event: Attend a workshop in Venice between day 3 and day 9.
# 3: Krakow     – Planned stay: 6 days.
# 4: Lyon       – Planned stay: 2 days.
#
# Total planned days = 3 + 7 + 7 + 6 + 2 = 25.
# There will be 4 flight days, so effective trip duration = 25 - 4 = 21 days.
# -----------------------------------------------------------------------------

cities = ["Manchester", "Istanbul", "Venice", "Krakow", "Lyon"]
durations = [3, 7, 7, 6, 2]

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional):
#
# "Manchester and Venice"   -> (0,2) and (2,0)
# "Manchester and Istanbul" -> (0,1) and (1,0)
# "Venice and Istanbul"     -> (2,1) and (1,2)
# "Istanbul and Krakow"     -> (1,3) and (3,1)
# "Venice and Lyon"         -> (2,4) and (4,2)
# "Lyon and Istanbul"       -> (4,1) and (1,4)
# "Manchester and Krakow"   -> (0,3) and (3,0)
# -----------------------------------------------------------------------------

allowed_flights = {
    (0,2), (2,0),
    (0,1), (1,0),
    (2,1), (1,2),
    (1,3), (3,1),
    (2,4), (4,2),
    (4,1), (1,4),
    (0,3), (3,0)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# pos[i]: the city visited at itinerary position i (i = 0,...,4).
#         They form a permutation of {0,...,4}.
#
# S[i]: the arrival day to the city at position i.
# The trip starts on day 1, so S[0] == 1.
#
# For the first city, effective stay = full planned duration.
# For subsequent cities, effective stay = (planned duration - 1) days,
# since one day is used for the flight.
#
# Trip end constraint:
#   S[4] + (effective stay for the last city) - 1 == 21.
# -----------------------------------------------------------------------------

n = 5
s = Solver()

# Itinerary: permutation of cities 0..4.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days: S[i] is the arrival day at the city at position i.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 0: S[0] = 1.
# For position 1: S[1] = S[0] + (full stay of city at pos[0]).
# For positions i >= 2: S[i] = S[i-1] + (planned duration of city at pos[i-1] - 1).
# -----------------------------------------------------------------------------

# For position 1:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    /* else (pos[0]==4): */ durations[4])))
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
        /* else (pos[i-1]==4): */ durations[4] - 1)))
    )

# Trip end constraint:
last_eff = If(n == 1,
              If(pos[n-1] == 0, durations[0],
              If(pos[n-1] == 1, durations[1],
              If(pos[n-1] == 2, durations[2],
              If(pos[n-1] == 3, durations[3],
              durations[4])))),
              If(pos[n-1] == 0, durations[0] - 1,
              If(pos[n-1] == 1, durations[1] - 1,
              If(pos[n-1] == 2, durations[2] - 1,
              If(pos[n-1] == 3, durations[3] - 1,
              durations[4] - 1))))
s.add(S_days[n-1] + last_eff - 1 == 21)

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
# (a) Manchester (city 0) wedding event: must be attended between day 1 and day 3.
#     The effective visit period is:
#       If first city: [S, S + durations[0] - 1],
#       Else: [S, S + (durations[0]-1) - 1]
#     We require this interval to intersect the window [1, 3],
#     i.e. S <= 3 and (S + effective - 1) >= 1.
#
# (b) Venice (city 2) workshop event: must be attended between day 3 and day 9.
#     Similarly, require S <= 9 and (S + effective - 1) >= 3.
# -----------------------------------------------------------------------------
for i in range(n):
    # Manchester event (city 0)
    s.add(
        If(pos[i] == 0,
           And(
               S_days[i] <= 3,
               If(i == 0,
                  S_days[i] + durations[0] - 1 >= 1,
                  S_days[i] + (durations[0] - 1) - 1 >= 1)
           ),
           True)
    )
    # Venice event (city 2)
    s.add(
        If(pos[i] == 2,
           And(
               S_days[i] <= 9,
               If(i == 0,
                  S_days[i] + durations[2] - 1 >= 3,
                  S_days[i] + (durations[2] - 1) - 1 >= 3)
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
        eff = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        departure = arrivals[i] + eff - 1
        print(f" Position {i+1}: {city:11s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] +
                          (durations[itinerary[n-1]] if n == 1 else durations[itinerary[n-1]] - 1) - 1)
    print(f"Trip ends on day: {trip_end}")
else:
    print("No valid trip plan could be found.")