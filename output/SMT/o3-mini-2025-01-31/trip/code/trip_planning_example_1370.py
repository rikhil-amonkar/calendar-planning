from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions:
#
# We have 9 cities:
# 0: Santorini  – planned stay: 5 days.
#                 Event: meet your friends between day 25 and day 29.
# 1: Krakow     – planned stay: 5 days.
#                 Event: attend a wedding between day 18 and day 22.
# 2: Paris      – planned stay: 5 days.
#                 Event: meet a friend between day 11 and day 15.
# 3: Vilnius    – planned stay: 3 days.
# 4: Munich     – planned stay: 5 days.
# 5: Geneva     – planned stay: 2 days.
# 6: Amsterdam  – planned stay: 4 days.
# 7: Budapest   – planned stay: 5 days.
# 8: Split      – planned stay: 4 days.
#
# Total planned days = 5 + 5 + 5 + 3 + 5 + 2 + 4 + 5 + 4 = 38.
# There will be 8 flight days (one less than the number of cities), so the effective
# trip duration is 38 - 8 = 30 days.
# -----------------------------------------------------------------------------

cities = ["Santorini", "Krakow", "Paris", "Vilnius", "Munich", "Geneva", "Amsterdam", "Budapest", "Split"]
durations = [5, 5, 5, 3, 5, 2, 4, 5, 4]

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# Provided flights (with indices corresponding to our cities):
#
# "Paris and Krakow"          -> (2,1) and (1,2)
# "Paris and Amsterdam"       -> (2,6) and (6,2)
# "Paris and Split"           -> (2,8) and (8,2)
# "from Vilnius to Munich"    -> directional: (3,4)
# "Paris and Geneva"          -> (2,5) and (5,2)
# "Amsterdam and Geneva"      -> (6,5) and (5,6)
# "Munich and Split"          -> (4,8) and (8,4)
# "Split and Krakow"          -> (8,1) and (1,8)
# "Munich and Amsterdam"      -> (4,6) and (6,4)
# "Budapest and Amsterdam"    -> (7,6) and (6,7)
# "Split and Geneva"          -> (8,5) and (5,8)
# "Vilnius and Split"         -> (3,8) and (8,3)
# "Munich and Geneva"         -> (4,5) and (5,4)
# "Munich and Krakow"         -> (4,1) and (1,4)
# "from Krakow to Vilnius"    -> directional: (1,3)
# "Vilnius and Amsterdam"     -> (3,6) and (6,3)
# "Budapest and Paris"        -> (7,2) and (2,7)
# "Krakow and Amsterdam"      -> (1,6) and (6,1)
# "Vilnius and Paris"         -> (3,2) and (2,3)
# "Budapest and Geneva"       -> (7,5) and (5,7)
# "Split and Amsterdam"       -> (8,6) and (6,8)
# "Santorini and Geneva"      -> (0,5) and (5,0)
# "Amsterdam and Santorini"   -> (6,0) and (0,6)
# "Munich and Budapest"       -> (4,7) and (7,4)
# "Munich and Paris"          -> (4,2) and (2,4)
# -----------------------------------------------------------------------------

allowed_flights = {
    (2,1), (1,2),
    (2,6), (6,2),
    (2,8), (8,2),
    (3,4),                # Vilnius -> Munich (directional)
    (2,5), (5,2),
    (6,5), (5,6),
    (4,8), (8,4),
    (8,1), (1,8),
    (4,6), (6,4),
    (7,6), (6,7),
    (8,5), (5,8),
    (3,8), (8,3),
    (4,5), (5,4),
    (4,1), (1,4),
    (1,3),               # Krakow -> Vilnius (directional)
    (3,6), (6,3),
    (7,2), (2,7),
    (1,6), (6,1),
    (3,2), (2,3),
    (7,5), (5,7),
    (8,6), (6,8),
    (0,5), (5,0),
    (6,0), (0,6),
    (4,7), (7,4),
    (4,2), (2,4)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# pos[i]: the city visited at itinerary position i (i=0,...,8). They must form
#         a permutation of {0,..,8}.
#
# S[i]: the arrival day at the city visited at position i.
# S[0] = 1 (trip starts on day 1).
#
# Effective stay:
#   For the first city: full planned duration.
#   For subsequent cities: (planned duration - 1) (because a flight day is used)
#
# Trip end condition:
#   S[8] + (effective stay for last city) - 1 == 30.
# -----------------------------------------------------------------------------

n = 9
s = Solver()

# Itinerary order as a permutation of 0..8
pos = IntVector('pos', n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days at each city.
S_days = IntVector('S', n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For i = 0: S_days[0] == 1.
# For position 1: S_days[1] = S_days[0] + (full planned duration for city at pos[0]).
# For positions i>=2: S_days[i] = S_days[i-1] + (planned duration of city at pos[i-1] - 1).
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
    If(pos[0] == 7, durations[7],
    /* else (pos[0]==8): */ durations[8]))))))))
)

# For positions 2 through 8:
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
        /* else: */ durations[8] - 1))))))))
    )

# Trip end constraint:
last_eff = If(n == 1,
              If(pos[n-1]==0, durations[0],
              If(pos[n-1]==1, durations[1],
              If(pos[n-1]==2, durations[2],
              If(pos[n-1]==3, durations[3],
              If(pos[n-1]==4, durations[4],
              If(pos[n-1]==5, durations[5],
              If(pos[n-1]==6, durations[6],
              If(pos[n-1]==7, durations[7],
              durations[8]))))))),
              If(pos[n-1]==0, durations[0] - 1,
              If(pos[n-1]==1, durations[1] - 1,
              If(pos[n-1]==2, durations[2] - 1,
              If(pos[n-1]==3, durations[3] - 1,
              If(pos[n-1]==4, durations[4] - 1,
              If(pos[n-1]==5, durations[5] - 1,
              If(pos[n-1]==6, durations[6] - 1,
              If(pos[n-1]==7, durations[7] - 1,
              durations[8] - 1))))))))
s.add(S_days[n-1] + last_eff - 1 == 30)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
# For each consecutive pair (pos[i], pos[i+1]), there must be a direct flight.
# -----------------------------------------------------------------------------
for i in range(n - 1):
    valid_flight = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                valid_flight.append(And(pos[i]==a, pos[i+1]==b))
    s.add(Or(valid_flight))

# -----------------------------------------------------------------------------
# Event constraints:
#
# For a visited city with an event, we impose that its effective visit interval
# intersects the event window.
#
# Event (a): Santorini (city 0) meet friends between day 25 and day 29.
#    Constraint: S_days[i] <= 29 and (S_days[i] + effective_stay - 1) >= 25.
#
# Event (b): Krakow (city 1) wedding between day 18 and day 22.
#    Constraint: S_days[i] <= 22 and (S_days[i] + effective_stay - 1) >= 18.
#
# Event (c): Paris (city 2) meet a friend between day 11 and day 15.
#    Constraint: S_days[i] <= 15 and (S_days[i] + effective_stay - 1) >= 11.
# -----------------------------------------------------------------------------
for i in range(n):
    # Event for Santorini (city 0)
    s.add(
        If(pos[i] == 0,
           And(
               S_days[i] <= 29,
               If(i == 0,
                  S_days[i] + durations[0] - 1 >= 25,
                  S_days[i] + (durations[0] - 1) - 1 >= 25)
           ),
           True)
    )
    # Event for Krakow (city 1)
    s.add(
        If(pos[i] == 1,
           And(
               S_days[i] <= 22,
               If(i == 0,
                  S_days[i] + durations[1] - 1 >= 18,
                  S_days[i] + (durations[1] - 1) - 1 >= 18)
           ),
           True)
    )
    # Event for Paris (city 2)
    s.add(
        If(pos[i] == 2,
           And(
               S_days[i] <= 15,
               If(i == 0,
                  S_days[i] + durations[2] - 1 >= 11,
                  S_days[i] + (durations[2] - 1) - 1 >= 11)
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
        effective = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city:12s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] if n==1 else (durations[itinerary[n-1]] - 1)) - 1)
    print(f"Trip ends on day: {trip_end}")
else:
    print("No valid trip plan could be found.")