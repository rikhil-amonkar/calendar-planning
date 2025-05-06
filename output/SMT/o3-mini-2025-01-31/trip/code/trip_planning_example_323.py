from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 4 cities:
# 0: Split  – 5 days.
#    Event: Annual show in Split between day 7 and day 11.
# 1: Oslo   – 2 days.
# 2: London – 7 days.
#    Event: Visit relatives in London between day 1 and day 7.
# 3: Porto  – 5 days.
#
# Total planned days = 5 + 2 + 7 + 5 = 19.
# There are 3 flights (transitions), so effective trip duration = 19 - 3 = 16 days.
#
# Note:
# - In the first visited city, the full planned duration applies.
# - In every subsequent city, one day is “lost” for the flight, so effective duration = duration - 1.
# -----------------------------------------------------------------------------
cities    = ["Split", "Oslo", "London", "Porto"]
durations = [5,       2,      7,       5]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    0: (7, 11),  # Split: annual show between day 7 and day 11.
    2: (1, 7)    # London: visit relatives between day 1 and day 7.
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# Given flights:
# - London and Oslo  -> bidirectional: (London,Oslo) and (Oslo,London) i.e. (2,1) and (1,2)
# - Split and Oslo   -> bidirectional: (Split,Oslo) and (Oslo,Split) i.e. (0,1) and (1,0)
# - Oslo and Porto   -> bidirectional: (Oslo,Porto) and (Porto,Oslo) i.e. (1,3) and (3,1)
# - London and Split -> bidirectional: (London,Split) and (Split,London) i.e. (2,0) and (0,2)
# -----------------------------------------------------------------------------
allowed_flights = {
    (2,1), (1,2),
    (0,1), (1,0),
    (1,3), (3,1),
    (2,0), (0,2)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation of the 4 cities:
#   pos[i] : the city index visited at itinerary position i (0 <= i < 4).
#   S[i]   : the arrival day at the city visited at position i.
#
# For the first city (i == 0): the visit interval is [S[0], S[0] + duration - 1].
# For every subsequent city (i >= 1): the effective visit interval is [S[i], S[i] + duration - 2].
#
# The departure day from the final city must equal total_trip = 16.
# -----------------------------------------------------------------------------
n = 4
total_trip = 16
s = Solver()

# Permutation: each city appears exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival day for each city.
S = IntVector("S", n)
s.add(S[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions for computing durations.
def full_duration(i):
    # For the first visited city, full planned duration is used.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

def effective_duration(i):
    # For subsequent cities, effective duration = duration - 1.
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#   S[1] = S[0] + (full_duration of city at pos[0]).
# For positions 2 to n-1:
#   S[i] = S[i-1] + (effective_duration of city at pos[i-1]).
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the final city (position n-1), the departure day is:
#   If it's the first city: S[n-1] + (duration - 1),
#   Otherwise: S[n-1] + (duration - 1) from effective duration.
# We model this as: S[n-1] + effective_duration(n-1) - 1 == total_trip.
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair of cities (positions i and i+1),
# there must be a direct flight between them.
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
# For each city with an event, if it is visited at position i,
# its visit interval must cover the event window.
#
# The visit interval is:
#   - if i == 0: [S[i], S[i] + duration - 1]
#   - if i >= 1: [S[i], S[i] + duration - 2]
# -----------------------------------------------------------------------------
for i in range(n):
    for city, (ev_start, ev_end) in events.items():
        s.add(
            If(pos[i] == city,
               And(
                   S[i] <= ev_end,
                   If(i == 0,
                      S[i] + durations[city] - 1 >= ev_start,
                      S[i] + durations[city] - 2 >= ev_start)
               ),
               True)
        )

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
        print(f" Position {i+1}: {city_name:6s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    
    # Final trip end day:
    last_city = itinerary[-1]
    if n - 1 == 0:
        final_departure = arrivals[-1] + durations[last_city] - 1
    else:
        final_departure = arrivals[-1] + durations[last_city] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")