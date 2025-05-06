from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 3 cities:
# 0: Venice   – 6 days.
#      Event: Attend a workshop in Venice between day 5 and day 10.
# 1: Mykonos  – 2 days.
# 2: Vienna   – 4 days.
#
# Total planned days = 6 + 2 + 4 = 12.
# There are 2 flight transitions, so the effective trip duration = 12 - 2 = 10 days.
#
# Note:
# - For the first visited city, the full planned duration applies.
# - For every subsequent city, one day is "lost" because of the flight (effective duration = duration - 1).
# -----------------------------------------------------------------------------
cities    = ["Venice", "Mykonos", "Vienna"]
durations = [6,         2,         4]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    0: (5, 10)  # Venice: workshop between day 5 and day 10
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# Given flights (bidirectional unless stated otherwise):
# - Mykonos and Vienna       -> (Mykonos,Vienna) and (Vienna,Mykonos), i.e., (1,2) and (2,1)
# - Vienna and Venice        -> (Vienna,Venice) and (Venice,Vienna), i.e., (2,0) and (0,2)
#
# Notice: Direct flight between Venice and Mykonos is not available.
# Therefore, the only itinerary that meets the connectivity requirement is:
#    Venice → Vienna → Mykonos
# -----------------------------------------------------------------------------
allowed_flights = {
    (1,2), (2,1),
    (2,0), (0,2)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation (ordering) of the 3 cities:
#   pos[i] : the city index visited at itinerary position i (for 0 <= i < 3).
#   S[i]   : the arrival day at the city visited at position i.
#
# For the first city (i==0): the visit interval is [S[0], S[0] + duration - 1].
# For every subsequent city (i>=1): the effective visit interval is [S[i], S[i] + duration - 2].
#
# The departure day from the final city must equal total_trip = 10.
# -----------------------------------------------------------------------------
n = 3
total_trip = 10
s = Solver()

# Permutation: each city appears exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days for each city.
S = IntVector("S", n)
s.add(S[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions for calculating durations.
def full_duration(i):
    # For the first visited city, its full planned duration is used.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

def effective_duration(i):
    # For subsequent cities, effective duration = (duration - 1) due to flight time.
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#    S[1] = S[0] + (full_duration of city at pos[0]).
# For positions i >= 2:
#    S[i] = S[i-1] + (effective_duration of city at pos[i-1]).
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the final city (position n-1):
#    If city is not the first, its departure day is S[n-1] + (duration - 1).
# This must equal total_trip (10).
# -----------------------------------------------------------------------------
# (Note: Our formulation subtracts one day per flight, so we adjust by subtracting 1.)
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair in the itinerary (positions i and i+1),
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
#    - if i == 0: [S[i], S[i] + duration - 1]
#    - if i >= 1: [S[i], S[i] + duration - 2]
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
        city_idx = itinerary[i]
        city_name = cities[city_idx]
        if i == 0:
            departure = arrivals[i] + durations[city_idx] - 1
        else:
            departure = arrivals[i] + durations[city_idx] - 2
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