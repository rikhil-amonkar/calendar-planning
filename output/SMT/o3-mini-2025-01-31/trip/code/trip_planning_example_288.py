from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 4 cities (indices and details):
# 0: Stuttgart  – 5 days.
#    Workshop event in Stuttgart: must attend on some day between 11 and 15.
#    For a visit to cover the event, the visit interval must intersect [11,15].
#    (Note: When not visited first, the effective visit interval is [S, S + 5 – 2].)
#
# 1: Manchester – 7 days.
#    Wedding event in Manchester: must attend on some day between 1 and 7.
#    (For first city, visit interval is [S, S+7–1], for later cities it is [S, S+7–2].)
#
# 2: Madrid     – 4 days.
#    No event.
#
# 3: Vienna     – 2 days.
#    No event.
#
# The sum of planned durations = 5 + 7 + 4 + 2 = 18 days.
# With 3 flights between the 4 cities, one travel day is “lost” per flight.
# Hence, the effective trip duration = 18 – 3 = 15 days.
# -----------------------------------------------------------------------------
cities    = ["Stuttgart", "Manchester", "Madrid", "Vienna"]
durations = [5,            7,          4,       2]

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional unless stated otherwise):
# - Vienna and Stuttgart: (3,0) and (0,3)
# - Manchester and Vienna: (1,3) and (3,1)
# - Madrid and Vienna: (2,3) and (3,2)
# - Manchester and Stuttgart: (1,0) and (0,1)
# - Manchester and Madrid: (1,2) and (2,1)
# -----------------------------------------------------------------------------
allowed_flights = {
    (3, 0), (0, 3),
    (1, 3), (3, 1),
    (2, 3), (3, 2),
    (1, 0), (0, 1),
    (1, 2), (2, 1)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Time model details:
#
# We represent the itinerary as a permutation of the 4 cities:
#   pos[i] is the index of the city visited in itinerary position i, for i in {0,1,2,3}.
#
# The arrival day for the city in position i is S[i]. The trip starts on day 1:
#   S[0] = 1.
#
# For the first city (i==0) the whole planned duration is used:
#   Visit interval = [S[0], S[0] + durations[city] - 1].
#
# For any subsequent city (i>=1), one day is “lost” to the flight:
#   Visit interval = [S[i], S[i] + durations[city] - 2].
#
# The final departure day must equal the total trip length (15).
# For i >= 1 (non-first city), the departure day = S[i] + durations[city] - 2.
# -----------------------------------------------------------------------------
n = 4
total_trip = 15
s = Solver()

# Permutation: each city appears exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days for each visited city.
S = IntVector("S", n)
s.add(S[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# -----------------------------------------------------------------------------
# Helper functions to retrieve the planned duration for a city at position i.
#
# For the first city we use the full planned duration.
def full_duration(i):
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

# For positions beyond the first, one day is lost due to flying.
def effective_duration(i):
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For city in position 1: arrival is = S[0] + (full duration of first city)
s.add(S[1] == S[0] + full_duration(0))
# For positions 2 and beyond: arrival is = previous arrival + (effective duration of previous city)
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))

# -----------------------------------------------------------------------------
# Final trip end constraint:
#
# For the final (non-first) city (position n-1), the departure day equals:
#    departure = S[n-1] + durations[city] - 2
# We require that departure equals total_trip.
# -----------------------------------------------------------------------------
s.add(S[n-1] + sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Direct flight connectivity constraints:
#
# For every consecutive pair in the itinerary (city at pos[i] to pos[i+1]),
# there must be an allowed direct flight.
# -----------------------------------------------------------------------------
for i in range(n - 1):
    options = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                options.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(options))

# -----------------------------------------------------------------------------
# Event constraints:
#
# Wedding in Manchester (city index 1) must occur on a day between 1 and 7.
# (It suffices that the visit interval intersects [1,7].)
#
# For the visit interval:
# - If Manchester is visited as the first city (i==0): interval = [S, S + 7 - 1].
#   Then we require S[0] <= 7. Since S[0] = 1, this automatically holds.
#
# - If visited as a later city (i>=1): interval = [S, S + 7 - 2].
#   We require that the visit interval intersects [1,7]. A sufficient condition is:
#     S[i] <= 7.
s.add(  # For every itinerary position, if the city is Manchester then arrival must be no later than day 7.
    And([If(pos[i] == 1, S[i] <= 7, True) for i in range(n)])
)

# Workshop in Stuttgart (city index 0) must occur on a day between 11 and 15.
# For Stuttgart the visit interval is:
# - If Stuttgart is visited first (i==0): interval = [S, S + 5 - 1] = [S, S+4].
#   To cover any day between 11 and 15 we would need S <= 15 and S+4 >= 11.
#   But S[0] is fixed to 1, and 1+4 = 5 which does not reach 11.
#   Therefore, Stuttgart cannot be the first city.
s.add(pos[0] != 0)

# - If Stuttgart is visited later (i>=1): interval = [S, S + 5 - 2] = [S, S+3].
#   To have the workshop (some day between 11 and 15) occur during the visit,
#   it is sufficient that the interval reaches 11; i.e., S + 3 >= 11  =>  S >= 8.
for i in range(1, n):
    s.add(If(pos[i] == 0, S[i] >= 8, True))
    # Also, to ensure the event window is not missed, we require that the arrival
    # is no later than the workshop end:
    s.add(If(pos[i] == 0, S[i] <= 15, True))

# -----------------------------------------------------------------------------
# Solve the scheduling problem.
# -----------------------------------------------------------------------------
if s.check() == sat:
    m = s.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals  = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city_index = itinerary[i]
        city_name = cities[city_index]
        if i == 0:
            departure = arrivals[i] + durations[city_index] - 1
        else:
            departure = arrivals[i] + durations[city_index] - 2
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    if n == 1:
        final_departure = arrivals[0] + durations[itinerary[0]] - 1
    else:
        final_departure = arrivals[-1] + durations[itinerary[-1]] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")