from z3 import Solver, Int, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions:
#
# We have 5 cities:
# 0: Nice      – planned stay: 5 days.
#               Event: visit relatives between day 1 and day 5.
# 1: Krakow    – planned stay: 6 days.
# 2: Dublin    – planned stay: 7 days.
# 3: Lyon      – planned stay: 4 days.
# 4: Frankfurt – planned stay: 2 days.
#               Event: meet your friends between day 19 and day 20.
#
# Total planned days = 5 + 6 + 7 + 4 + 2 = 24.
# Since the trip starts in the first city (full stay) and each flight uses 1 day,
# the effective trip duration is:
#       24 - (5 - 1) = 24 - 4 = 20 days.
# -----------------------------------------------------------------------------

cities = ["Nice", "Krakow", "Dublin", "Lyon", "Frankfurt"]
durations = [5, 6, 7, 4, 2]

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional):
#
# - Nice and Dublin         -> (0,2) and (2,0)
# - Dublin and Frankfurt    -> (2,4) and (4,2)
# - Dublin and Krakow       -> (2,1) and (1,2)
# - Krakow and Frankfurt    -> (1,4) and (4,1)
# - Lyon and Frankfurt      -> (3,4) and (4,3)
# - Nice and Frankfurt      -> (0,4) and (4,0)
# - Lyon and Dublin         -> (3,2) and (2,3)
# - Nice and Lyon           -> (0,3) and (3,0)
# -----------------------------------------------------------------------------

allowed_flights = {
    (0,2), (2,0),
    (2,4), (4,2),
    (2,1), (1,2),
    (1,4), (4,1),
    (3,4), (4,3),
    (0,4), (4,0),
    (3,2), (2,3),
    (0,3), (3,0)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# pos[i]: the city visited at itinerary position i, for i=0,...,4.
# They must form a permutation of {0,1,2,3,4}.
#
# S[i]: the arrival day at the city visited at position i.
# The trip starts at day 1 (S[0] == 1).
#
# Notes on effective stay:
#  - For the first city visited, effective stay = full planned duration.
#  - For every subsequent city, one day is used for transit,
#    so effective stay = (planned duration - 1).
#
# The trip ends at day 20:
#    S[4] + (effective stay of city at pos[4]) - 1 == 20.
# -----------------------------------------------------------------------------

n = 5
s = Solver()

# Itinerary: a permutation of the city indices 0..4.
pos = IntVector('pos', n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days for each visited city.
S_days = IntVector('S', n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
# For position 0, S_days[0] == 1.
# For position 1: S_days[1] = S_days[0] + (full planned duration of city at pos[0]).
# For positions i>=2: S_days[i] = S_days[i-1] + (planned duration of city at pos[i-1] - 1).
# -----------------------------------------------------------------------------

# For position 1:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    /* else: */ durations[4]))))
)

# For positions 2 through 4:
for i in range(2, n):
    s.add(
        S_days[i] ==
        S_days[i-1] +
        If(pos[i-1] == 0, durations[0] - 1,
        If(pos[i-1] == 1, durations[1] - 1,
        If(pos[i-1] == 2, durations[2] - 1,
        If(pos[i-1] == 3, durations[3] - 1,
        /* else: */ durations[4] - 1))))
    )

# Trip end: For the last visited city,
# effective stay is full duration if it is the first city,
# otherwise (planned duration - 1). Its departure day is:
#   S_days[4] + effective - 1 == 20.
last_eff = If(n == 1,
              If(pos[n-1]==0, durations[0],
              If(pos[n-1]==1, durations[1],
              If(pos[n-1]==2, durations[2],
              If(pos[n-1]==3, durations[3],
              durations[4])))),
              If(pos[n-1]==0, durations[0] - 1,
              If(pos[n-1]==1, durations[1] - 1,
              If(pos[n-1]==2, durations[2] - 1,
              If(pos[n-1]==3, durations[3] - 1,
              durations[4] - 1))))
s.add(S_days[n-1] + last_eff - 1 == 20)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
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
# (a) Nice (city 0): Visit relatives between day 1 and day 5.
#     For a visit at position i:
#       - If i == 0: effective stay = durations[0] (5 days).
#         Constraint: S_days[i] <= 5  and S_days[i] + 5 - 1 >= 1.
#       - Else: effective stay = durations[0] - 1 (4 days).
#         Constraint: S_days[i] <= 5 and S_days[i] + 4 - 1 >= 1.
#
# (b) Frankfurt (city 4): Meet friends between day 19 and day 20.
#     For a visit at position i:
#       - If i == 0: effective stay = durations[4] (2 days).
#         Constraint: S_days[i] <= 20 and S_days[i] + 2 - 1 >= 19.
#       - Else: effective stay = durations[4] - 1 (1 day).
#         Constraint: S_days[i] <= 20 and S_days[i] + 1 - 1 >= 19.
# -----------------------------------------------------------------------------
for i in range(n):
    # Event for Nice (city 0)
    s.add(
        If(pos[i] == 0,
           And(
               S_days[i] <= 5,
               If(i == 0, S_days[i] + durations[0] - 1 >= 1,
                         S_days[i] + (durations[0] - 1) - 1 >= 1)
           ),
           True)
    )
    
    # Event for Frankfurt (city 4)
    s.add(
        If(pos[i] == 4,
           And(
               S_days[i] <= 20,
               If(i == 0, S_days[i] + durations[4] - 1 >= 19,
                         S_days[i] + (durations[4] - 1) - 1 >= 19)
           ),
           True)
    )

# -----------------------------------------------------------------------------
# Solve the scheduling problem.
# -----------------------------------------------------------------------------
if s.check() == sat:
    m = s.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals = [m.evaluate(S_days[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city = cities[itinerary[i]]
        # Calculate effective stay:
        eff = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        departure = arrivals[i] + eff - 1
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    end_day = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] if n==1 else (durations[itinerary[n-1]] - 1)) - 1)
    print(f"Trip ends on day: {end_day}")
else:
    print("No valid trip plan could be found.")