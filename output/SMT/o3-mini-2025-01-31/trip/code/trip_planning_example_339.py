from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 4 cities:
# 0: Riga    – 7 days.
#    Event: Wedding in Riga between day 11 and day 17.
# 1: Budapest – 7 days.
# 2: Paris    – 4 days.
# 3: Warsaw   – 2 days.
#    Event: Annual show in Warsaw from day 1 to day 2.
#
# Total planned days = 7 + 7 + 4 + 2 = 20.
# There are 3 flight transitions (for 4 cities), so effective trip duration = 20 - 3 = 17 days.
#
# Note:
# - For the first visited city, the full planned duration is used.
# - For every subsequent city, one day is "lost" due to the flight (effective duration = duration - 1).
# -----------------------------------------------------------------------------
cities    = ["Riga", "Budapest", "Paris", "Warsaw"]
durations = [7,       7,         4,      2]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    0: (11, 17),  # Riga: wedding between day 11 and day 17.
    3: (1, 2)     # Warsaw: annual show from day 1 to day 2.
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# The provided flights are:
# - Warsaw and Budapest   -> (Warsaw, Budapest) and (Budapest, Warsaw)         => (3,1) and (1,3)
# - Warsaw and Riga       -> (Warsaw, Riga) and (Riga, Warsaw)                     => (3,0) and (0,3)
# - Budapest and Paris    -> (Budapest, Paris) and (Paris, Budapest)               => (1,2) and (2,1)
# - Warsaw and Paris      -> (Warsaw, Paris) and (Paris, Warsaw)                   => (3,2) and (2,3)
# - Paris and Riga        -> (Paris, Riga) and (Riga, Paris)                       => (2,0) and (0,2)
# -----------------------------------------------------------------------------
allowed_flights = {
    (3,1), (1,3),
    (3,0), (0,3),
    (1,2), (2,1),
    (3,2), (2,3),
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
# The departure day from the final city must equal total_trip = 17.
# -----------------------------------------------------------------------------
n = 4
total_trip = 17
s = Solver()

# Permutation: each city appears exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days for each city.
S = IntVector("S", n)
s.add(S[0] == 1)  # The trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions to compute durations:
def full_duration(i):
    # For the first visited city, full planned duration applies.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

def effective_duration(i):
    # For subsequent cities, effective duration = duration - 1.
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#   S[1] = S[0] + (full_duration of city at pos[0]).
# For positions 2..n-1:
#   S[i] = S[i-1] + (effective_duration of city at pos[i-1]).
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the final city (position n-1):
#   Departure day = S[n-1] + (duration - 1) if first city, or (duration - 1) from effective duration.
# Our formulation: S[n-1] + effective_duration(n-1) - 1 == total_trip.
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair (i, i+1) in the itinerary,
# there must be a direct flight between the cities.
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
# For each city with an event, if that city is visited at itinerary position i,
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
        print(f" Position {i+1}: {city_name:8s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    
    # Compute final trip end day.
    last_city = itinerary[-1]
    if n - 1 == 0:
        final_departure = arrivals[-1] + durations[last_city] - 1
    else:
        final_departure = arrivals[-1] + durations[last_city] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")