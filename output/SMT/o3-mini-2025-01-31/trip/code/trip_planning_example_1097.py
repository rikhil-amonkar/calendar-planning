from z3 import Solver, Int, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions:
#
# We have 8 cities:
# 0: Reykjavik  – planned stay: 4 days.
# 1: Riga       – planned stay: 2 days.
#                Event: meet a friend between day 4 and day 5.
# 2: Oslo       – planned stay: 3 days.
# 3: Lyon       – planned stay: 5 days.
# 4: Dubrovnik  – planned stay: 2 days.
#                Event: attend a wedding between day 7 and day 8.
# 5: Madrid     – planned stay: 2 days.
# 6: Warsaw     – planned stay: 4 days.
# 7: London     – planned stay: 3 days.
#
# Total planned days = 4+2+3+5+2+2+4+3 = 25.
# There will be 7 flight days (one per transition) so the effective trip duration is:
#       25 - 7 = 18 days.
# -----------------------------------------------------------------------------

cities = ["Reykjavik", "Riga", "Oslo", "Lyon", "Dubrovnik", "Madrid", "Warsaw", "London"]
durations = [4, 2, 3, 5, 2, 2, 4, 3]

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# The given flights (with indices) are:
# - Warsaw and Reykjavik      -> (6,0) and (0,6)
# - Oslo and Madrid            -> (2,5) and (5,2)
# - Warsaw and Riga            -> (6,1) and (1,6)
# - Lyon and London            -> (3,7) and (7,3)
# - Madrid and London          -> (5,7) and (7,5)
# - Warsaw and London          -> (6,7) and (7,6)
# - from Reykjavik to Madrid   -> directional: (0,5) only.
# - Warsaw and Oslo            -> (6,2) and (2,6)
# - Oslo and Dubrovnik         -> (2,4) and (4,2)
# - Oslo and Reykjavik         -> (2,0) and (0,2)
# - Riga and Oslo              -> (1,2) and (2,1)
# - Oslo and Lyon              -> (2,3) and (3,2)
# - Oslo and London            -> (2,7) and (7,2)
# - London and Reykjavik       -> (7,0) and (0,7)
# - Warsaw and Madrid          -> (6,5) and (5,6)
# - Madrid and Lyon            -> (5,3) and (3,5)
# - Dubrovnik and Madrid       -> (4,5) and (5,4)
# -----------------------------------------------------------------------------

# We'll use a set of allowed flight pairs (a, b). For directional flights we'll only insert the allowed direction.
allowed_flights = {
    (6, 0), (0, 6),              # Warsaw <-> Reykjavik
    (2, 5), (5, 2),              # Oslo <-> Madrid
    (6, 1), (1, 6),              # Warsaw <-> Riga
    (3, 7), (7, 3),              # Lyon <-> London
    (5, 7), (7, 5),              # Madrid <-> London
    (6, 7), (7, 6),              # Warsaw <-> London
    (0, 5),                     # directional: Reykjavik -> Madrid only
    (6, 2), (2, 6),              # Warsaw <-> Oslo
    (2, 4), (4, 2),              # Oslo <-> Dubrovnik
    (2, 0), (0, 2),              # Oslo <-> Reykjavik
    (1, 2), (2, 1),              # Riga <-> Oslo
    (2, 3), (3, 2),              # Oslo <-> Lyon
    (2, 7), (7, 2),              # Oslo <-> London
    (7, 0), (0, 7),              # London <-> Reykjavik
    (6, 5), (5, 6),              # Warsaw <-> Madrid
    (5, 3), (3, 5),              # Madrid <-> Lyon
    (4, 5), (5, 4)               # Dubrovnik <-> Madrid
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# pos[i]: city visited at itinerary position i, for i = 0,...,7.
# These should be a permutation of {0,1,...,7}.
#
# S[i]: arrival day at the city visited at position i.
# The trip starts at day 1, so S[0] = 1.
#
# The effective stay in a city depends on its position:
#   - If it is the first city, effective stay = full planned duration.
#   - Otherwise, effective stay = planned duration - 1 (since one day is allocated for flight)
#
# This gives the sequential arrival day constraints and the final trip end constraint.
# -----------------------------------------------------------------------------

n = 8
s = Solver()

# Itinerary: permutation of cities 0 ... 7.
pos = IntVector('pos', n)
s.add(Distinct(pos))
for i in range(n):
    s.add(pos[i] >= 0, pos[i] < n)

# Arrival days for each city.
S_days = IntVector('S', n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# The arrival day for position 0 is 1.
# For position 1: S[1] = S[0] + full duration of city at pos[0].
# For positions i >= 2: S[i] = S[i-1] + (planned_duration(pos[i-1]) - 1).
# -----------------------------------------------------------------------------

# For position 1:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    If(pos[0] == 4, durations[4],
    If(pos[0] == 5, durations[5],
    If(pos[0] == 6, durations[6],
    /* else: */ durations[7])))))))
)

# For positions 2 through 7:
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
        /* else: */ durations[7] - 1)))))))
    )

# Trip end constraint:
# Let last effective duration = full duration if first city else duration-1.
last_eff = If(n == 1,
              If(pos[n-1]==0, durations[0],
              If(pos[n-1]==1, durations[1],
              If(pos[n-1]==2, durations[2],
              If(pos[n-1]==3, durations[3],
              If(pos[n-1]==4, durations[4],
              If(pos[n-1]==5, durations[5],
              If(pos[n-1]==6, durations[6],
              durations[7])))))),
              If(pos[n-1]==0, durations[0] - 1,
              If(pos[n-1]==1, durations[1] - 1,
              If(pos[n-1]==2, durations[2] - 1,
              If(pos[n-1]==3, durations[3] - 1,
              If(pos[n-1]==4, durations[4] - 1,
              If(pos[n-1]==5, durations[5] - 1,
              If(pos[n-1]==6, durations[6] - 1,
              durations[7] - 1)))))))
s.add(S_days[n-1] + last_eff - 1 == 18)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair (pos[i], pos[i+1]) there must be a direct flight
# from the city at pos[i] to the city at pos[i+1].
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
# (a) Riga (city index 1) - Meet a friend between day 4 and day 5.
#     Let effective stay = durations[1] if city at pos[i] is first,
#                         or durations[1]-1 otherwise.
#     We require that the time interval [S, S + effective stay - 1] covers [4, 5],
#     i.e. S <= 5 and S + effective stay - 1 >= 4.
#
# (b) Dubrovnik (city index 4) - Wedding between day 7 and day 8.
#     Similarly, require S <= 8 and S + effective stay - 1 >= 7.
# -----------------------------------------------------------------------------
for i in range(n):
    # For Riga (city 1)
    s.add(
        If(pos[i] == 1,
           And(
               S_days[i] <= 5,
               If(i == 0,
                  S_days[i] + durations[1] - 1 >= 4,
                  S_days[i] + (durations[1] - 1) - 1 >= 4)
           ),
           True)
    )
    # For Dubrovnik (city 4)
    s.add(
        If(pos[i] == 4,
           And(
               S_days[i] <= 8,
               If(i == 0,
                  S_days[i] + durations[4] - 1 >= 7,
                  S_days[i] + (durations[4] - 1) - 1 >= 7)
           ),
           True)
    )

# -----------------------------------------------------------------------------
# Solve the scheduling problem.
# -----------------------------------------------------------------------------
if s.check() == sat:
    m = s.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrival = [m.evaluate(S_days[i]).as_long() for i in range(n)]
    trip_end = m.evaluate(S_days[n-1] + 
                (durations[itinerary[n-1]] if n==1 else (durations[itinerary[n-1]] - 1)) - 1)
    print("Trip Itinerary:")
    for i in range(n):
        city = cities[itinerary[i]]
        # Effective stay is full duration for first city; otherwise (planned - 1)
        eff = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        departure = arrival[i] + eff - 1
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrival[i]:2d} | Departure: Day {departure:2d}")
    print(f"Trip ends on day: {trip_end}")
else:
    print("No valid trip plan could be found.")