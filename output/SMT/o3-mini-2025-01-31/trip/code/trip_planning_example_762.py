from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions:
#
# We have 6 cities:
# 0: Dublin   – planned stay: 3 days.
#              Event: meet your friends between day 7 and day 9.
# 1: Madrid   – planned stay: 2 days.
#              Event: visit relatives between day 2 and day 3.
# 2: Oslo     – planned stay: 3 days.
# 3: London   – planned stay: 2 days.
# 4: Vilnius  – planned stay: 3 days.
# 5: Berlin   – planned stay: 5 days.
#              Event: attend a wedding between day 3 and day 7.
#
# Total planned days = 3 + 2 + 3 + 2 + 3 + 5 = 18.
# There will be 5 flight days (one for each transition), so the effective
# trip duration is 18 - 5 = 13 days.
# -----------------------------------------------------------------------------

cities = ["Dublin", "Madrid", "Oslo", "London", "Vilnius", "Berlin"]
durations = [3, 2, 3, 2, 3, 5]

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional unless stated otherwise):
#
# "London and Madrid"     -> (3,1) and (1,3)
# "Oslo and Vilnius"      -> (2,4) and (4,2)
# "Berlin and Vilnius"    -> (5,4) and (4,5)
# "Madrid and Oslo"       -> (1,2) and (2,1)
# "Madrid and Dublin"     -> (1,0) and (0,1)
# "London and Oslo"       -> (3,2) and (2,3)
# "Madrid and Berlin"     -> (1,5) and (5,1)
# "Berlin and Oslo"       -> (5,2) and (2,5)
# "Dublin and Oslo"       -> (0,2) and (2,0)
# "London and Dublin"     -> (3,0) and (0,3)
# "London and Berlin"     -> (3,5) and (5,3)
# "Berlin and Dublin"     -> (5,0) and (0,5)
# -----------------------------------------------------------------------------

allowed_flights = {
    (3,1), (1,3),
    (2,4), (4,2),
    (5,4), (4,5),
    (1,2), (2,1),
    (1,0), (0,1),
    (3,2), (2,3),
    (1,5), (5,1),
    (5,2), (2,5),
    (0,2), (2,0),
    (3,0), (0,3),
    (3,5), (5,3),
    (5,0), (0,5)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# pos[i]: the city visited at itinerary position i (i = 0,...,5). They form a permutation
#         of {0,...,5}.
#
# S[i]: the arrival day to the city at position i.
# The trip starts on day 1, so S[0] == 1.
#
# For the first city, effective stay = full duration.
# For subsequent cities, effective stay = (planned duration - 1),
# because one day is taken up by the flight.
#
# The trip must end on day 13, i.e.:
#   S[5] + (effective stay for last city) - 1 == 13.
# -----------------------------------------------------------------------------

n = 6
s = Solver()

# Itinerary order is a permutation of city indices.
pos = IntVector('pos', n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector
S_days = IntVector('S', n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# City at position 0: S[0] = 1.
# For position 1: S[1] = S[0] + (full planned duration of the city at pos[0]).
# For positions i >= 2: S[i] = S[i-1] + (planned duration of city at pos[i-1] - 1).
# -----------------------------------------------------------------------------

# Constraint for position 1:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    If(pos[0] == 4, durations[4],
    /* else (pos[0]==5): */ durations[5])))))
)

# For positions 2 to 5:
for i in range(2, n):
    s.add(
        S_days[i] ==
        S_days[i-1] +
        If(pos[i-1] == 0, durations[0] - 1,
        If(pos[i-1] == 1, durations[1] - 1,
        If(pos[i-1] == 2, durations[2] - 1,
        If(pos[i-1] == 3, durations[3] - 1,
        If(pos[i-1] == 4, durations[4] - 1,
        /* else (pos[i-1]==5): */ durations[5] - 1)))))
    )

# Trip end constraint:
last_eff = If(n == 1,
              If(pos[n-1] == 0, durations[0],
              If(pos[n-1] == 1, durations[1],
              If(pos[n-1] == 2, durations[2],
              If(pos[n-1] == 3, durations[3],
              If(pos[n-1] == 4, durations[4],
              durations[5]))))),
              If(pos[n-1] == 0, durations[0] - 1,
              If(pos[n-1] == 1, durations[1] - 1,
              If(pos[n-1] == 2, durations[2] - 1,
              If(pos[n-1] == 3, durations[3] - 1,
              If(pos[n-1] == 4, durations[4] - 1,
              durations[5] - 1)))))
s.add(S_days[n-1] + last_eff - 1 == 13)

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
# Event for Dublin (city 0):
#   Effective stay:
#      if first city: durations[0] = 3, else: durations[0] - 1 = 2.
#   Must hold: S[i] <= 9 and (S[i] + effective - 1) >= 7.
#
# Event for Madrid (city 1):
#   Planned duration 2:
#      if first city: effective = 2, else: effective = 1.
#   Must hold: S[i] <= 3 and (S[i] + effective - 1) >= 2.
#
# Event for Berlin (city 5):
#   Planned duration 5:
#      if first city: effective = 5, else: effective = 4.
#   Must hold: S[i] <= 7 and (S[i] + effective - 1) >= 3.
# -----------------------------------------------------------------------------
for i in range(n):
    # Dublin event (city 0)
    s.add(
        If(pos[i] == 0,
           And(
               S_days[i] <= 9,
               If(i == 0,
                  S_days[i] + durations[0] - 1 >= 7,
                  S_days[i] + (durations[0] - 1) - 1 >= 7)
           ),
           True)
    )
    # Madrid event (city 1)
    s.add(
        If(pos[i] == 1,
           And(
               S_days[i] <= 3,
               If(i == 0,
                  S_days[i] + durations[1] - 1 >= 2,
                  S_days[i] + (durations[1] - 1) - 1 >= 2)
           ),
           True)
    )
    # Berlin event (city 5)
    s.add(
        If(pos[i] == 5,
           And(
               S_days[i] <= 7,
               If(i == 0,
                  S_days[i] + durations[5] - 1 >= 3,
                  S_days[i] + (durations[5] - 1) - 1 >= 3)
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
        print(f" Position {i+1}: {city:8s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] if n==1 else (durations[itinerary[n-1]] - 1)) - 1)
    print(f"Trip ends on day: {trip_end}")
else:
    print("No valid trip plan could be found.")