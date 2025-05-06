from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions:
#
# We have 8 cities:
# 0: Vienna      – planned stay: 4 days.
# 1: Lyon        – planned stay: 3 days.
# 2: Edinburgh   – planned stay: 4 days.
#                   Event: attend an annual show from day 5 to day 8.
# 3: Reykjavik   – planned stay: 5 days.
# 4: Stuttgart   – planned stay: 5 days.
# 5: Manchester  – planned stay: 2 days.
# 6: Split       – planned stay: 5 days.
#                   Event: attend a wedding from day 19 to day 23.
# 7: Prague      – planned stay: 4 days.
#
# Total planned days = 4 + 3 + 4 + 5 + 5 + 2 + 5 + 4 = 32.
# There will be 7 flight days (one less than number of cities), so the effective
# trip duration is 32 - 7 = 25 days.
# -----------------------------------------------------------------------------

cities = ["Vienna", "Lyon", "Edinburgh", "Reykjavik", "Stuttgart", "Manchester", "Split", "Prague"]
durations = [4, 3, 4, 5, 5, 2, 5, 4]

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# Provided flights:
# - from Reykjavik to Stuttgart         -> directional: (3,4)
# - Stuttgart and Split                  -> (4,6) and (6,4)
# - Stuttgart and Vienna                 -> (4,0) and (0,4)
# - Prague and Manchester                -> (7,5) and (5,7)
# - Edinburgh and Prague                 -> (2,7) and (7,2)
# - from Manchester to Split             -> directional: (5,6)
# - Prague and Vienna                    -> (7,0) and (0,7)
# - Vienna and Manchester                -> (0,5) and (5,0)
# - Prague and Split                     -> (7,6) and (6,7)
# - Vienna and Lyon                      -> (0,1) and (1,0)
# - Stuttgart and Edinburgh              -> (4,2) and (2,4)
# - Split and Lyon                       -> (6,1) and (1,6)
# - Stuttgart and Manchester             -> (4,5) and (5,4)
# - Prague and Lyon                      -> (7,1) and (1,7)
# - Reykjavik and Vienna                 -> (3,0) and (0,3)
# - Prague and Reykjavik                 -> (7,3) and (3,7)
# - Vienna and Split                     -> (0,6) and (6,0)
# -----------------------------------------------------------------------------

allowed_flights = {
    (3,4),                              # Reykjavik -> Stuttgart (directional)
    (4,6), (6,4),                       # Stuttgart <-> Split
    (4,0), (0,4),                       # Stuttgart <-> Vienna
    (7,5), (5,7),                       # Prague <-> Manchester
    (2,7), (7,2),                       # Edinburgh <-> Prague
    (5,6),                              # Manchester -> Split (directional)
    (7,0), (0,7),                       # Prague <-> Vienna
    (0,5), (5,0),                       # Vienna <-> Manchester
    (7,6), (6,7),                       # Prague <-> Split
    (0,1), (1,0),                       # Vienna <-> Lyon
    (4,2), (2,4),                       # Stuttgart <-> Edinburgh
    (6,1), (1,6),                       # Split <-> Lyon
    (4,5), (5,4),                       # Stuttgart <-> Manchester
    (7,1), (1,7),                       # Prague <-> Lyon
    (3,0), (0,3),                       # Reykjavik <-> Vienna
    (7,3), (3,7),                       # Prague <-> Reykjavik
    (0,6), (6,0)                        # Vienna <-> Split
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# pos[i]: the city visited at itinerary position i for i=0,...,7.
#        They must be a permutation of {0,1,...,7}.
#
# S[i]: the arrival day at the city visited at position i.
# The trip starts on day 1 (S[0] == 1).
#
# For the first city, the effective stay is the full planned duration.
# For every subsequent city, one day is taken for the flight, so the effective
# stay = (planned duration - 1).
#
# The final trip end condition:
#    S[7] + (effective stay for the last city) - 1 == 25.
# -----------------------------------------------------------------------------

n = 8
s = Solver()

# Itinerary: permutation of cities.
pos = IntVector('pos', n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days.
S_days = IntVector('S', n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For i = 0: S[0] == 1.
# For position 1: S[1] = S[0] + full planned duration of city at pos[0].
# For positions i>=2: S[i] = S[i-1] + (planned duration of city at pos[i-1] - 1).
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
        /* else: */ durations[7] - 1)))))))
    )

# Trip end constraint:
last_eff = If(n == 1, 
              If(pos[n-1] == 0, durations[0],
              If(pos[n-1] == 1, durations[1],
              If(pos[n-1] == 2, durations[2],
              If(pos[n-1] == 3, durations[3],
              If(pos[n-1] == 4, durations[4],
              If(pos[n-1] == 5, durations[5],
              If(pos[n-1] == 6, durations[6],
              durations[7])))))),
              If(pos[n-1] == 0, durations[0] - 1,
              If(pos[n-1] == 1, durations[1] - 1,
              If(pos[n-1] == 2, durations[2] - 1,
              If(pos[n-1] == 3, durations[3] - 1,
              If(pos[n-1] == 4, durations[4] - 1,
              If(pos[n-1] == 5, durations[5] - 1,
              If(pos[n-1] == 6, durations[6] - 1,
              durations[7] - 1)))))))
s.add(S_days[n-1] + last_eff - 1 == 25)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
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
# (a) Edinburgh (city 2): Attend an annual show from day 5 to day 8.
#     For position i where city == 2, we require:
#       S_days[i] <= 8 and (S_days[i] + effective stay - 1) >= 5.
#
# (b) Split (city 6): Attend a wedding from day 19 to day 23.
#     For position i where city == 6, we require:
#       S_days[i] <= 23 and (S_days[i] + effective stay - 1) >= 19.
# -----------------------------------------------------------------------------
for i in range(n):
    # Event for Edinburgh (city 2)
    s.add(
        If(pos[i] == 2,
           And(
               S_days[i] <= 8,
               If(i == 0,
                  S_days[i] + durations[2] - 1 >= 5,
                  S_days[i] + (durations[2] - 1) - 1 >= 5)
           ),
           True)
    )
    # Event for Split (city 6)
    s.add(
        If(pos[i] == 6,
           And(
               S_days[i] <= 23,
               If(i == 0,
                  S_days[i] + durations[6] - 1 >= 19,
                  S_days[i] + (durations[6] - 1) - 1 >= 19)
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
        # Effective stay:
        effective = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] if n==1 else (durations[itinerary[n-1]] - 1)) - 1)
    print(f"Trip ends on day: {trip_end}")
else:
    print("No valid trip plan could be found.")