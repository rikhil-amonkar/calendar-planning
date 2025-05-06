from z3 import Solver, Int, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions:
#
# We have 5 cities:
# 0: Hamburg   – planned stay: 7 days.
# 1: Munich    – planned stay: 6 days.
# 2: Manchester– planned stay: 2 days;
#                Event: visit relatives between day 19 and day 20.
# 3: Lyon      – planned stay: 2 days;
#                Event: annual show between day 13 and day 14.
# 4: Split     – planned stay: 7 days.
#
# Total planned days = 7 + 6 + 2 + 2 + 7 = 24.
# Since the trip starts in the first city (full stay) and each flight day costs 1 day,
# the effective trip duration is:
#      24 - (5 - 1) = 24 - 4 = 20 days.
# -----------------------------------------------------------------------------

cities = ["Hamburg", "Munich", "Manchester", "Lyon", "Split"]
durations = [7, 6, 2, 2, 7]

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# The given flights are:
# - Split and Munich          (bidirectional: (4,1) and (1,4))
# - Munich and Manchester     (bidirectional: (1,2) and (2,1))
# - Hamburg and Manchester    (bidirectional: (0,2) and (2,0))
# - Hamburg and Munich        (bidirectional: (0,1) and (1,0))
# - Split and Lyon            (bidirectional: (4,3) and (3,4))
# - Lyon and Munich           (bidirectional: (3,1) and (1,3))
# - Hamburg and Split         (bidirectional: (0,4) and (4,0))
# - from Manchester to Split  (directional: only (2,4))
# -----------------------------------------------------------------------------

# Define a set of allowed flight pairs. For most pairs we add them in both orders.
allowed_flights = {
    (4, 1), (1, 4),   # Split <-> Munich
    (1, 2), (2, 1),   # Munich <-> Manchester
    (0, 2), (2, 0),   # Hamburg <-> Manchester
    (0, 1), (1, 0),   # Hamburg <-> Munich
    (4, 3), (3, 4),   # Split <-> Lyon
    (3, 1), (1, 3),   # Lyon <-> Munich
    (0, 4), (4, 0),   # Hamburg <-> Split
    # Directional flight: from Manchester to Split only.
    (2, 4)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# pos[i]: the city visited at itinerary position i (i = 0,...,4). 
#         They should form a permutation of {0,1,2,3,4}.
#
# S[i]: the arrival day at the ith visited city.
# The trip starts at day 1: S[0] == 1.
#
# For the first city in the itinerary, the effective stay is the full planned duration.
# For every subsequent city, one day is spent in transit so that the effective stay
# is (planned duration - 1).
#
# The trip end constraint: S[4] + (effective duration of last city) - 1 == 20.
# -----------------------------------------------------------------------------

n = 5
s = Solver()

# Itinerary positions: a permutation of 0..4.
pos = IntVector('pos', n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days for each city.
S_days = IntVector('S', n)
s.add(S_days[0] == 1)  # trip starts at day 1
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Define sequential arrival day constraints.
#
# For position 0, effective duration = durations[ city ].
# For any position i>=1, effective duration = durations[ city ] - 1,
# because one day is used for the flight from the previous city.
#
# So for i = 1: S[1] = S[0] + (durations[ pos[0] ])
# For i >= 2: S[i] = S[i-1] + (durations[ pos[i-1] ] - 1).
# -----------------------------------------------------------------------------

# Helper: effective stay at position i given previous city's planned duration.
def effective_duration(position, city_index):
    # If the city is visited first (i == 0), effective duration = planned duration.
    # Otherwise, effective duration = planned duration - 1.
    return If(position == 0, durations[city_index], durations[city_index] - 1)

# For position 1, use city at pos[0] (which is first city).
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    /* else: */ durations[4])))
)

# Positions 2 through 4:
for i in range(2, n):
    s.add(
        S_days[i] ==
        S_days[i-1] +
        If(pos[i-1] == 0, durations[0] - 1,
        If(pos[i-1] == 1, durations[1] - 1,
        If(pos[i-1] == 2, durations[2] - 1,
        If(pos[i-1] == 3, durations[3] - 1,
        /* else: */ durations[4] - 1)))
    )

# Trip end constraint:
# Let effective_duration_last = (if last city is visited as first then durations[city] else durations[city]-1)
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
              durations[4] - 1)))))
s.add(S_days[n-1] + last_eff - 1 == 20)

# -----------------------------------------------------------------------------
# Flight connectivity constraints.
#
# For each consecutive pair (pos[i], pos[i+1]) in the itinerary,
# a direct flight must exist from the city at pos[i] to the city at pos[i+1].
# (Notice: one flight is directional: from Manchester (2) to Split (4))
# -----------------------------------------------------------------------------
for i in range(n - 1):
    flights = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                flights.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(flights))

# -----------------------------------------------------------------------------
# Event constraints.
#
# (1) In Manchester (city index 2), visit relatives between day 19 and day 20.
#     For the visit, the effective stay interval should intersect with [19,20]:
#     Let eff = durations[2] if first city else durations[2]-1.
#     For i == 0: require S[i] <= 20 and S[i] + durations[2] - 1 >= 19.
#     For i > 0: require S[i] <= 20 and S[i] >= 19   (since effective stay is 1 day).
#
# (2) In Lyon (city index 3), annual show from day 13 to day 14.
#     For i == 0: require S[i] <= 14 and S[i] + durations[3] - 1 >= 13.
#     For i > 0: require S[i] <= 14 and S[i] in [13,14]  (since effective stay is 1 day).
# -----------------------------------------------------------------------------

for i in range(n):
    # For Manchester: city index 2.
    s.add(
        If(pos[i] == 2,
           And(
               S_days[i] <= 20,
               If(i == 0, S_days[i] + durations[2] - 1 >= 19,
                          S_days[i] >= 19)
           ),
           True)
    )
    
    # For Lyon: city index 3.
    s.add(
        If(pos[i] == 3,
           And(
               S_days[i] <= 14,
               If(i == 0, S_days[i] + durations[3] - 1 >= 13,
                          And(S_days[i] >= 13, S_days[i] <= 14))
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
    end_day = m.evaluate(S_days[n-1] + 
                (durations[itinerary[n-1]] if n==1 else (durations[itinerary[n-1]] - 1)) - 1)
    
    print("Trip Itinerary:")
    for i in range(n):
        city = cities[itinerary[i]]
        # Calculate effective duration:
        effective = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        departure = arrival[i] + effective - 1
        print(f" Position {i+1}: {city:11s} | Arrival: Day {arrival[i]:2d} | Departure: Day {departure:2d}")
    print(f"Trip ends on day: {end_day}")
else:
    print("No valid trip plan could be found.")