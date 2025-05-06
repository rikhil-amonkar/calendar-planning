from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions:
#
# We have 10 cities:
# 0: Venice     – planned stay: 3 days.
# 1: Reykjavik  – planned stay: 2 days.
# 2: Munich     – planned stay: 3 days.
#                 Event: annual show in Munich between day 4 and day 6.
# 3: Santorini  – planned stay: 3 days.
#                 Event: visit relatives in Santorini between day 8 and day 10.
# 4: Manchester – planned stay: 3 days.
# 5: Porto      – planned stay: 3 days.
# 6: Bucharest  – planned stay: 5 days.
# 7: Tallinn    – planned stay: 4 days.
# 8: Valencia   – planned stay: 2 days.
#                 Event: attend a workshop in Valencia between day 14 and day 15.
# 9: Vienna     – planned stay: 5 days.
#
# Total planned days = 3 + 2 + 3 + 3 + 3 + 3 + 5 + 4 + 2 + 5 = 33.
# There will be 9 flight days (one per transition), so the effective trip duration is
# 33 - 9 = 24 days.
# -----------------------------------------------------------------------------

cities = ["Venice", "Reykjavik", "Munich", "Santorini", "Manchester", "Porto", "Bucharest", "Tallinn", "Valencia", "Vienna"]
durations = [3, 2, 3, 3, 3, 3, 5, 4, 2, 5]

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional unless stated otherwise):
#
# "Bucharest and Manchester"   -> (6,4) and (4,6)
# "Munich and Venice"          -> (2,0) and (0,2)
# "Santorini and Manchester"   -> (3,4) and (4,3)
# "Vienna and Reykjavik"       -> (9,1) and (1,9)
# "Venice and Santorini"       -> (0,3) and (3,0)
# "Munich and Porto"           -> (2,5) and (5,2)
# "Valencia and Vienna"        -> (8,9) and (9,8)
# "Manchester and Vienna"      -> (4,9) and (9,4)
# "Porto and Vienna"           -> (5,9) and (9,5)
# "Venice and Manchester"      -> (0,4) and (4,0)
# "Santorini and Vienna"       -> (3,9) and (9,3)
# "Munich and Manchester"      -> (2,4) and (4,2)
# "Munich and Reykjavik"       -> (2,1) and (1,2)
# "Bucharest and Valencia"     -> (6,8) and (8,6)
# "Venice and Vienna"          -> (0,9) and (9,0)
# "Bucharest and Vienna"       -> (6,9) and (9,6)
# "Porto and Manchester"       -> (5,4) and (4,5)
# "Munich and Vienna"          -> (2,9) and (9,2)
# "Valencia and Porto"         -> (8,5) and (5,8)
# "Munich and Bucharest"       -> (2,6) and (6,2)
# "Tallinn and Munich"         -> (7,2) and (2,7)
# "Santorini and Bucharest"    -> (3,6) and (6,3)
# "Munich and Valencia"        -> (2,8) and (8,2)
# -----------------------------------------------------------------------------

allowed_flights = {
    (6,4), (4,6),
    (2,0), (0,2),
    (3,4), (4,3),
    (9,1), (1,9),
    (0,3), (3,0),
    (2,5), (5,2),
    (8,9), (9,8),
    (4,9), (9,4),
    (5,9), (9,5),
    (0,4), (4,0),
    (3,9), (9,3),
    (2,4), (4,2),
    (2,1), (1,2),
    (6,8), (8,6),
    (0,9), (9,0),
    (6,9), (9,6),
    (5,4), (4,5),
    (2,9), (9,2),
    (8,5), (5,8),
    (2,6), (6,2),
    (7,2), (2,7),
    (3,6), (6,3),
    (2,8), (8,2)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# pos[i]: the city visited at itinerary position i (i=0,...,9) and
#         they form a permutation of {0,...,9}.
#
# S[i]: the arrival day at the city at itinerary position i.
# The trip starts on day 1 so S[0] == 1.
#
# Effective stay length:
#   For the first city: full planned duration.
#   For subsequent cities: (planned duration - 1) days,
#   because one day is used for the flight from the previous city.
#
# The trip end constraint:
#   S[9] + (effective stay for the last city) - 1 == 24.
# -----------------------------------------------------------------------------

n = 10
s = Solver()

# Itinerary is a permutation of city indices.
pos = IntVector('pos', n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector.
S_days = IntVector('S', n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 0: S[0] = 1.
# For position 1: S[1] = S[0] + (full planned duration for city at pos[0]).
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
    If(pos[0] == 7, durations[7],
    If(pos[0] == 8, durations[8],
    /* else (pos[0]==9): */ durations[9])))))))))
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
        /* else (pos[i-1]==9): */ durations[9] - 1))))))))))
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
              durations[9] - 1))))))))              
s.add(S_days[n-1] + last_eff - 1 == 24)

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
# (a) Munich (city 2) event: Annual show from day 4 to day 6.
#     We require: arrival day <= 6 and (arrival + effective stay - 1) >= 4.
#
# (b) Santorini (city 3) event: Relatives visit between day 8 and day 10.
#     We require: arrival day <= 10 and departure >= 8.
#
# (c) Valencia (city 8) event: Workshop between day 14 and day 15.
#     We require: arrival day <= 15 and departure >= 14.
#
# Note: effective stay = full duration if the city is visited first,
#       else (planned duration - 1).
# -----------------------------------------------------------------------------
for i in range(n):
    # Munich event (city 2)
    s.add(
        If(pos[i] == 2,
           And(
               S_days[i] <= 6,
               If(i == 0,
                  S_days[i] + durations[2] - 1 >= 4,
                  S_days[i] + (durations[2] - 1) - 1 >= 4)
           ),
           True)
    )
    # Santorini event (city 3)
    s.add(
        If(pos[i] == 3,
           And(
               S_days[i] <= 10,
               If(i == 0,
                  S_days[i] + durations[3] - 1 >= 8,
                  S_days[i] + (durations[3] - 1) - 1 >= 8)
           ),
           True)
    )
    # Valencia event (city 8)
    s.add(
        If(pos[i] == 8,
           And(
               S_days[i] <= 15,
               If(i == 0,
                  S_days[i] + durations[8] - 1 >= 14,
                  S_days[i] + (durations[8] - 1) - 1 >= 14)
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
        # determine effective stay:
        eff = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        departure = arrivals[i] + eff - 1
        print(f" Position {i+1:2d}: {city:12s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] if n==1 else (durations[itinerary[n-1]] - 1)) - 1)
    print(f"Trip ends on day: {trip_end}")
else:
    print("No valid trip plan could be found.")