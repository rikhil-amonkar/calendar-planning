from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 3 cities:
# 0: Vilnius  – 4 days.
# 1: Munich   – 3 days.
# 2: Mykonos  – 7 days.
#
# Total planned days = 4 + 3 + 7 = 14.
# There are 2 flight transitions, so effective trip duration = 14 - 2 = 12 days.
#
# Notes:
# - The trip starts on day 1.
# - In the first city, you enjoy its full planned duration.
# - In every subsequent city, one day is "lost" due to the flight.
# -----------------------------------------------------------------------------

cities    = ["Vilnius", "Munich", "Mykonos"]
durations = [4,         3,       7]

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# The allowed flights are:
# - "from Vilnius to Munich" -> one-way (0,1)
# - "Munich and Mykonos"       -> bidirectional (1,2) and (2,1)
#
# -----------------------------------------------------------------------------
allowed_flights = {
    (0, 1),    # from Vilnius to Munich
    (1, 2), (2, 1)  # Munich <-> Mykonos
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We model an itinerary as an ordering (a permutation) of the 3 cities:
#   pos[i] : index of the city visited at itinerary position i, for i = 0,1,2.
#   S[i]   : arrival day at the city visited at position i.
#
# For a city at itinerary position i:
#   If i == 0: departure day = S[i] + durations[city] - 1.
#   If i >= 1: departure day = S[i] + (durations[city] - 1) - 1.
#
# The departure day of the final city must equal day 12.
# -----------------------------------------------------------------------------

n = 3
s = Solver()

# Itinerary positions (as a permutation of cities 0..2)
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#   S[1] = S[0] + (full planned duration of the city at pos[0]).
# For positions i >= 2:
#   S[i] = S[i-1] + (duration of city at pos[i-1] - 1).
# -----------------------------------------------------------------------------
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    /* pos[0] == 2 */ durations[2]))
)

for i in range(2, n):
    s.add(
        S_days[i] ==
        S_days[i-1] +
        If(pos[i-1] == 0, durations[0] - 1,
        If(pos[i-1] == 1, durations[1] - 1,
        /* pos[i-1] == 2 */ durations[2] - 1))
    )

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the final city (position n-1), effective stay = (duration - 1),
# so departure day = S_days[n-1] + (duration - 1) - 1 must equal 12.
# -----------------------------------------------------------------------------
last_effective = If(pos[n-1] == 0, durations[0] - 1,
                If(pos[n-1] == 1, durations[1] - 1,
                durations[2] - 1))
s.add(S_days[n-1] + last_effective - 1 == 12)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair in the itinerary, there must be a direct flight.
# -----------------------------------------------------------------------------
for i in range(n - 1):
    options = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                options.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(options))

# -----------------------------------------------------------------------------
# Solve the scheduling problem.
# -----------------------------------------------------------------------------
if s.check() == sat:
    m = s.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals  = [m.evaluate(S_days[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city_index = itinerary[i]
        city_name = cities[city_index]
        # Effective stay: full duration for the first city; otherwise (duration - 1)
        effective = durations[city_index] if i == 0 else durations[city_index] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:8s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")