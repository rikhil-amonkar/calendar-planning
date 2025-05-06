from z3 import Solver, Int, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions, planned durations and event windows.
#
# We have 9 cities:
# 0: Naples     – planned stay: 3 days.
#         Event: Meet a friend in Naples between day 18 and day 20.
#
# 1: Valencia   – planned stay: 5 days.
#
# 2: Stuttgart  – planned stay: 2 days.
#
# 3: Split      – planned stay: 5 days.
#
# 4: Venice     – planned stay: 5 days.
#         Event: Attend a conference in Venice between day 6 and day 10.
#
# 5: Amsterdam  – planned stay: 4 days.
#
# 6: Nice       – planned stay: 2 days.
#         Event: Meet your friends in Nice between day 23 and day 24.
#
# 7: Barcelona  – planned stay: 2 days.
#         Event: Attend a workshop in Barcelona between day 5 and day 6.
#
# 8: Porto      – planned stay: 4 days.
#
# Total planned days = 3+5+2+5+5+4+2+2+4 = 32.
# Since the trip starts in the first city (full duration) and each flight (between cities)
# costs 1 day, the effective trip duration will be:
#       32 - (9-1) = 32 - 8 = 24 days.
# -----------------------------------------------------------------------------

cities = ["Naples", "Valencia", "Stuttgart", "Split", "Venice", 
          "Amsterdam", "Nice", "Barcelona", "Porto"]
durations = [3, 5, 2, 5, 5, 4, 2, 2, 4]

# -----------------------------------------------------------------------------
# Allowed direct flights (we assume bidirectional, so both orders count):
#
# Venice and Nice             -> (Venice, Nice)               : (4,6)
# Naples and Amsterdam        -> (Naples, Amsterdam)          : (0,5)
# Barcelona and Nice          -> (Barcelona, Nice)            : (7,6)
# Amsterdam and Nice          -> (Amsterdam, Nice)            : (5,6)
# Stuttgart and Valencia      -> (Stuttgart, Valencia)        : (2,1)
# Stuttgart and Porto         -> (Stuttgart, Porto)           : (2,8)
# Split and Stuttgart         -> (Split, Stuttgart)           : (3,2)
# Split and Naples            -> (Split, Naples)              : (3,0)
# Valencia and Amsterdam      -> (Valencia, Amsterdam)        : (1,5)
# Barcelona and Porto         -> (Barcelona, Porto)           : (7,8)
# Valencia and Naples         -> (Valencia, Naples)           : (1,0)
# Venice and Amsterdam        -> (Venice, Amsterdam)          : (4,5)
# Barcelona and Naples        -> (Barcelona, Naples)          : (7,0)
# Barcelona and Valencia      -> (Barcelona, Valencia)        : (7,1)
# Split and Amsterdam         -> (Split, Amsterdam)           : (3,5)
# Barcelona and Venice        -> (Barcelona, Venice)          : (7,4)
# Stuttgart and Amsterdam     -> (Stuttgart, Amsterdam)       : (2,5)
# Naples and Nice             -> (Naples, Nice)               : (0,6)
# Venice and Stuttgart        -> (Venice, Stuttgart)          : (4,2)
# Split and Barcelona         -> (Split, Barcelona)           : (3,7)
# Porto and Nice              -> (Porto, Nice)                : (8,6)
# Barcelona and Stuttgart     -> (Barcelona, Stuttgart)       : (7,2)
# Venice and Naples           -> (Venice, Naples)             : (4,0)
# Porto and Amsterdam         -> (Porto, Amsterdam)           : (8,5)
# Porto and Valencia          -> (Porto, Valencia)            : (8,1)
# Stuttgart and Naples        -> (Stuttgart, Naples)          : (2,0)
# Barcelona and Amsterdam     -> (Barcelona, Amsterdam)       : (7,5)
# -----------------------------------------------------------------------------

allowed_flight_pairs = {
    (4, 6),   # Venice - Nice
    (0, 5),   # Naples - Amsterdam
    (7, 6),   # Barcelona - Nice
    (5, 6),   # Amsterdam - Nice
    (2, 1),   # Stuttgart - Valencia
    (2, 8),   # Stuttgart - Porto
    (3, 2),   # Split - Stuttgart
    (3, 0),   # Split - Naples
    (1, 5),   # Valencia - Amsterdam
    (7, 8),   # Barcelona - Porto
    (1, 0),   # Valencia - Naples
    (4, 5),   # Venice - Amsterdam
    (7, 0),   # Barcelona - Naples
    (7, 1),   # Barcelona - Valencia
    (3, 5),   # Split - Amsterdam
    (7, 4),   # Barcelona - Venice
    (2, 5),   # Stuttgart - Amsterdam
    (0, 6),   # Naples - Nice
    (4, 2),   # Venice - Stuttgart
    (3, 7),   # Split - Barcelona
    (8, 6),   # Porto - Nice
    (7, 2),   # Barcelona - Stuttgart
    (4, 0),   # Venice - Naples
    (8, 5),   # Porto - Amsterdam
    (8, 1),   # Porto - Valencia
    (2, 0),   # Stuttgart - Naples
    (7, 5)    # Barcelona - Amsterdam
}

def flight_allowed(a, b):
    return ((a, b) in allowed_flight_pairs) or ((b, a) in allowed_flight_pairs)

# -----------------------------------------------------------------------------
# Create the Z3 solver and define decision variables.
#
# pos[i] : the city (an integer 0..8) visited at itinerary position i (i = 0,...,8).
# They must be a permutation of [0,..,8].
#
# S[i]   : the arrival day at the city visited at position i.
# The trip starts at day 1: S[0] == 1.
# For the first city, we use the full planned duration.
# For every subsequent city, a flight day is taken so the effective stay is (duration - 1).
#
# The trip end day is given by:
#    S[8] + effective_duration(last city) == 24,
# where effective_duration = durations[c] if visited first; otherwise durations[c] - 1.
# -----------------------------------------------------------------------------

n = 9
s = Solver()

# Itinerary (permutation of the city indices 0..8)
pos = IntVector('pos', n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival day for each visited city.
S_days = IntVector('S', n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# Sequential arrival day constraints.
# For the first city (position 0): effective duration = durations[city].
# For each subsequent city i (i>=1): S_days[i] = S_days[i-1] + (durations[pos[i-1]] - 1).

# Position 1:
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
    /* else: */ durations[8]))))))) 
)

for i in range(2, n):
    s.add(
        S_days[i] == S_days[i-1] +
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

# Trip end constraint: For the last city at position n-1, effective duration depends on its position:
# if first city then durations[city] else durations[city] - 1.
trip_end = Int("trip_end")
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
              # Otherwise if not first, effective duration = planned - 1.
              If(pos[n-1]==0, durations[0] - 1,
              If(pos[n-1]==1, durations[1] - 1,
              If(pos[n-1]==2, durations[2] - 1,
              If(pos[n-1]==3, durations[3] - 1,
              If(pos[n-1]==4, durations[4] - 1,
              If(pos[n-1]==5, durations[5] - 1,
              If(pos[n-1]==6, durations[6] - 1,
              If(pos[n-1]==7, durations[7] - 1,
              durations[8] - 1))))))))
s.add(trip_end == S_days[n-1] + last_eff)
s.add(trip_end == 24)

# -----------------------------------------------------------------------------
# Flight connectivity constraints: 
# For each pair of consecutive cities in the itinerary, there must be a direct flight.
# -----------------------------------------------------------------------------
for i in range(n - 1):
    possible = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                possible.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(possible))

# -----------------------------------------------------------------------------
# Event constraints:
# For each city with an event, we constrain its arrival day considering
# the effective stay interval, which is:
#   - If the city is the first in the itinerary, effective duration = durations[city].
#     Interval = [S, S + durations[city] - 1].
#   - Otherwise, effective duration = durations[city] - 1.
#     Interval = [S, S + (durations[city]-1) - 1] = [S, S + durations[city] - 2].
#
# (a) Naples (city 0), meet friend between day 18 and day 20.
#     Constraint: S <= 20 and S + (eff_duration - 1) >= 18.
# (b) Venice (city 4), conference between day 6 and day 10.
#     Constraint: S <= 10 and S + (eff_duration - 1) >= 6.
# (c) Nice (city 6), meet friends between day 23 and day 24.
#     Constraint: S <= 24 and S + (eff_duration - 1) >= 23.
# (d) Barcelona (city 7), workshop between day 5 and day 6.
#     Constraint: S <= 6 and S + (eff_duration - 1) >= 5.
# -----------------------------------------------------------------------------
for i in range(n):
    # For city 'Naples' (index 0)
    if_cond = (pos[i] == 0)
    s.add(If(if_cond,
             And( S_days[i] <= 20,
                  If(i == 0, S_days[i] + durations[0] - 1,
                      S_days[i] + (durations[0] - 1) - 1) >= 18),
             True))
    
    # For city 'Venice' (index 4)
    if_cond = (pos[i] == 4)
    s.add(If(if_cond,
             And( S_days[i] <= 10,
                  If(i == 0, S_days[i] + durations[4] - 1,
                      S_days[i] + (durations[4] - 1) - 1) >= 6),
             True))
    
    # For city 'Nice' (index 6)
    if_cond = (pos[i] == 6)
    s.add(If(if_cond,
             And( S_days[i] <= 24,
                  If(i == 0, S_days[i] + durations[6] - 1,
                      S_days[i] + (durations[6] - 1) - 1) >= 23),
             True))
    
    # For city 'Barcelona' (index 7)
    if_cond = (pos[i] == 7)
    s.add(If(if_cond,
             And( S_days[i] <= 6,
                  If(i == 0, S_days[i] + durations[7] - 1,
                      S_days[i] + (durations[7] - 1) - 1) >= 5),
             True))

# -----------------------------------------------------------------------------
# Solve the scheduling problem.
# -----------------------------------------------------------------------------
if s.check() == sat:
    m = s.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrival = [m.evaluate(S_days[i]).as_long() for i in range(n)]
    end_day  = m.evaluate(trip_end)
    
    print("Trip Itinerary:")
    for i in range(n):
        city = cities[itinerary[i]]
        # Effective duration: if first city -> full duration, else (planned - 1).
        effective = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        departure = arrival[i] + effective - 1
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrival[i]:2d} | Departure: Day {departure:2d}")
    print(f"Trip ends on day: {end_day}")
else:
    print("No valid trip plan could be found.")