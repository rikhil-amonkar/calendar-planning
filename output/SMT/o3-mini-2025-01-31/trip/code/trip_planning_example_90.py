from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions:
#
# We have 3 cities:
# 0: Vilnius   – Planned stay: 7 days.
# 1: Naples    – Planned stay: 5 days.
#               Event: Visit relatives in Naples between day 1 and day 5.
# 2: Vienna    – Planned stay: 7 days.
#
# Total planned days = 7 + 5 + 7 = 19.
# There will be 2 flight days (one per transition), so the effective trip duration is
# 19 - 2 = 17 days.
# -----------------------------------------------------------------------------

cities   = ["Vilnius", "Naples", "Vienna"]
durations = [7, 5, 7]

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional):
#
# "Naples and Vienna" -> (1,2) and (2,1)
# "Vienna and Vilnius" -> (2,0) and (0,2)
# -----------------------------------------------------------------------------

allowed_flights = {
    (1,2), (2,1),
    (2,0), (0,2)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# pos[i]: the city visited at itinerary position i (i = 0,1,2).
#         They form a permutation of {0,1,2}.
#
# S[i]: the arrival day at the city at position i.
# The trip starts on day 1 so S[0] == 1.
#
# Effective stay:
#   If city is visited as the first city, effective stay = full planned duration.
#   Otherwise, effective stay = (planned duration - 1) days (accounting for flight day).
#
# Trip end constraint:
#   S[2] + (effective stay for city at pos[2]) - 1 == 17.
# -----------------------------------------------------------------------------

n = 3
s = Solver()

# Itinerary permutation.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(pos[i] >= 0, pos[i] < n)

# Arrival days.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1: S[1] = S[0] + (full duration of city at pos[0])
# For position i >= 2: S[i] = S[i-1] + (planned duration of city at pos[i-1] - 1).
# -----------------------------------------------------------------------------

# Position 1 constraint:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    /* else pos[0]==2 */  durations[2]))
)

# Positions 2 constraint:
s.add(
    S_days[2] ==
    S_days[1] +
    If(pos[1] == 0, durations[0] - 1,
    If(pos[1] == 1, durations[1] - 1,
    /* else pos[1]==2 */  durations[2] - 1))
)

# Trip end constraint:
last_eff = If(pos[n-1] == 0, durations[0] - 1,
               If(pos[n-1] == 1, durations[1] - 1,
               durations[2] - 1))
s.add(S_days[n-1] + last_eff - 1 == 17)

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
# Event constraint:
#
# Naples (city 1) relatives visit event must happen between day 1 and day 5.
# Let effective stay at Naples be:
#   If first city: durations[1],
#   Else: durations[1] - 1.
# The visit period is [S, S + effective - 1].
# We require:
#    S <= 5 and (S + effective - 1) >= 1.
# -----------------------------------------------------------------------------
for i in range(n):
    s.add(
        If(pos[i] == 1,
           And(
               S_days[i] <= 5,
               If(i == 0,
                  S_days[i] + durations[1] - 1 >= 1,
                  S_days[i] + (durations[1] - 1) - 1 >= 1)
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
        print(f" Position {i+1}: {city:8s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] +
                          (durations[itinerary[n-1]] if n == 1 else durations[itinerary[n-1]] - 1) - 1)
    print(f"Trip ends on day: {trip_end}")
else:
    print("No valid trip plan could be found.")