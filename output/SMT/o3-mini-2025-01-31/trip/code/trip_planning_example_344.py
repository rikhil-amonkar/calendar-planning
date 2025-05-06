from z3 import Solver, Int, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations
#
# We have 4 cities:
# 0: Valencia   – planned stay of 6 days.
# 1: Athens     – planned stay of 6 days.
# 2: Naples     – planned stay of 5 days.
# 3: Zurich     – planned stay of 6 days.
#
# The total planned durations sum to 6+6+5+6 = 23.
# Since the trip begins in the first city (full duration) and every subsequent visit
# costs 1 day for a flight, the effective trip length is:
#      23 - (4-1) = 23 - 3 = 20 days.
# -----------------------------------------------------------------------------

cities = ["Valencia", "Athens", "Naples", "Zurich"]
durations = [6, 6, 5, 6]  # corresponding planned durations

# -----------------------------------------------------------------------------
# Allowed direct flights (assumed bidirectional):
# - Valencia <-> Naples
# - Valencia <-> Athens   (given as "from Valencia to Athens", assumed bidirectional)
# - Athens   <-> Naples
# - Zurich   <-> Naples
# - Athens   <-> Zurich
# - Zurich   <-> Valencia
# -----------------------------------------------------------------------------
allowed_flight_pairs = {
    (0, 2),  # Valencia - Naples
    (0, 1),  # Valencia - Athens
    (1, 2),  # Athens - Naples
    (3, 2),  # Zurich - Naples
    (1, 3),  # Athens - Zurich
    (3, 0)   # Zurich - Valencia
}

def flight_allowed(a, b):
    return ((a, b) in allowed_flight_pairs) or ((b, a) in allowed_flight_pairs)

# -----------------------------------------------------------------------------
# Create Z3 solver and decision variables.
#
# pos[i]: city visited at itinerary position i, i = 0,1,2,3.
# They form a permutation of {0, 1, 2, 3}.
#
# S[i]: the arrival day in city pos[i]. The trip starts at day 1.
# For the first city, the full planned duration is spent.
# For each subsequent city, one day is spent in transit so that the effective
# stay is (duration - 1).
# The constraint: S[3] + (duration(pos[3]) - 1) == 20.
# -----------------------------------------------------------------------------
n = 4

s = Solver()

# Itinerary: positions 0...3
pos = IntVector('pos', n)
s.add(Distinct(pos))
for i in range(n):
    s.add(pos[i] >= 0, pos[i] < 4)

# Arrival days for each city visited.
S_days = IntVector('S', n)
s.add(S_days[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential day constraints:
#
# For the first city (pos[0]), full planned duration is spent.
# For i = 1: S[1] == S[0] + duration(pos[0]).
# For i >= 2: S[i] == S[i-1] + (duration(pos[i-1]) - 1).
# -----------------------------------------------------------------------------
# Position 1:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    /* else: */ durations[3])))
)

# Positions 2 and 3:
for i in range(2, n):
    s.add(
        S_days[i] == S_days[i-1] +
        If(pos[i-1] == 0, durations[0] - 1,
        If(pos[i-1] == 1, durations[1] - 1,
        If(pos[i-1] == 2, durations[2] - 1,
        /* else: */ durations[3] - 1)))
    )

# The trip must end on day 20.
trip_end = Int("trip_end")
# Effective duration for the last city is: full duration if visited first, otherwise duration-1.
trip_end_expr = If(pos[n-1] == 0, durations[0],
                 If(pos[n-1] == 1, durations[1],
                 If(pos[n-1] == 2, durations[2],
                 /* else: */ durations[3])))
# But note: for the last city, since it is not preceded by a flight day (or rather, flight day already accounted),
# if it is not the first city we subtract 1.
trip_end_expr = If(n == 1, trip_end_expr, trip_end_expr - 1)
s.add(trip_end == S_days[n-1] + trip_end_expr)
s.add(trip_end == 20)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
# For each consecutive pair (pos[i], pos[i+1]), there must be a direct flight.
# -----------------------------------------------------------------------------
for i in range(n - 1):
    cons = []
    for a in range(4):
        for b in range(4):
            if flight_allowed(a, b):
                cons.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(cons))

# -----------------------------------------------------------------------------
# Event constraints:
#
# 1. Visit relatives in Athens between day 1 and day 6.
#    Athens is index 1. For any itinerary position i with pos[i]==1, require:
#         S_days[i] <= 6.
#
# 2. Attend a wedding in Naples between day 16 and day 20.
#    Naples is index 2.
#    For the city visited at position i if pos[i] == 2:
#      - If i==0, effective interval is [S_days[0], S_days[0] + durations[2] - 1] = [S, S+4].
#      - Otherwise, effective interval is [S_days[i], S_days[i] + durations[2] - 1 - 1] = [S, S+3].
#    We require that the effective interval covers at least some time between day 16 and 20.
#    For simplicity, we enforce:
#         S_days[i] <= 20   and   S_days[i] + (effective_duration - 1) >= 16.
#
#    Here, effective_duration = durations[2] if i==0 (i.e. 5), else durations[2] - 1 (i.e. 4).
# -----------------------------------------------------------------------------
for i in range(n):
    # Constraint for Athens (index 1)
    s.add(If(pos[i] == 1, S_days[i] <= 6, True))
    
    # Constraint for Naples (index 2) wedding.
    # For the first city, effective duration = 5, so the interval is [S, S+4].
    # For subsequent cities, effective duration = 4, so the interval is [S, S+3].
    if i == 0:
        s.add(If(pos[i] == 2, And(S_days[i] <= 20, S_days[i] + 4 >= 16), True))
    else:
        s.add(If(pos[i] == 2, And(S_days[i] <= 20, S_days[i] + 3 >= 16), True))

# -----------------------------------------------------------------------------
# Solve and output a trip plan
# -----------------------------------------------------------------------------
if s.check() == sat:
    m = s.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrival = [m.evaluate(S_days[i]).as_long() for i in range(n)]
    end_day = m.evaluate(trip_end)
    
    print("Trip Itinerary:")
    for i in range(n):
        city = cities[itinerary[i]]
        # Compute effective duration:
        # If this is the first city, full duration.
        # Otherwise, effective stay is (duration - 1) (since 1 day is taken by a flight).
        eff = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        departure = arrival[i] + eff - 1
        print(f" Position {i+1}: {city:8s} | Arrival: Day {arrival[i]:2d} | Departure: Day {departure:2d}")
    print(f"Trip ends on day: {end_day}")
else:
    print("No valid trip plan could be found.")