from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 5 cities (indices with details):
# 0: Paris     – 6 days.
# 1: Oslo      – 5 days.
#                Event: Visit relatives in Oslo between day 19 and day 23.
# 2: Porto     – 7 days.
# 3: Geneva    – 7 days.
#                Event: Attend a conference in Geneva between day 1 and day 7.
# 4: Reykjavik – 2 days.
#
# Total planned days = 6 + 5 + 7 + 7 + 2 = 27.
# There are 4 flights between cities, so effective trip duration = 27 - 4 = 23 days.
#
# Note:
# - In the first city you enjoy the full duration.
# - In every subsequent city, one day is "lost" due to the flight (effective stay = duration - 1).
# -----------------------------------------------------------------------------
cities    = ["Paris", "Oslo", "Porto", "Geneva", "Reykjavik"]
durations = [6,       5,     7,      7,       2]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    1: (19, 23),  # Oslo: Visit relatives between day 19 and day 23.
    3: (1, 7)     # Geneva: Conference between day 1 and day 7.
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# Flights are bidirectional:
# - Paris and Oslo       -> (Paris, Oslo) and (Oslo, Paris)         -> (0,1), (1,0)
# - Geneva and Oslo      -> (Geneva, Oslo) and (Oslo, Geneva)         -> (3,1), (1,3)
# - Porto and Paris      -> (Porto, Paris) and (Paris, Porto)         -> (2,0), (0,2)
# - Geneva and Paris     -> (Geneva, Paris) and (Paris, Geneva)       -> (3,0), (0,3)
# - Geneva and Porto     -> (Geneva, Porto) and (Porto, Geneva)       -> (3,2), (2,3)
# - Paris and Reykjavik  -> (Paris, Reykjavik) and (Reykjavik, Paris) -> (0,4), (4,0)
# - Reykjavik and Oslo   -> (Reykjavik, Oslo) and (Oslo, Reykjavik)   -> (4,1), (1,4)
# - Porto and Oslo       -> (Porto, Oslo) and (Oslo, Porto)           -> (2,1), (1,2)
# -----------------------------------------------------------------------------
allowed_flights = {
    (0,1), (1,0),
    (3,1), (1,3),
    (2,0), (0,2),
    (3,0), (0,3),
    (3,2), (2,3),
    (0,4), (4,0),
    (4,1), (1,4),
    (2,1), (1,2)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation (ordering) of the 5 cities:
#   pos[i]: the city index visited at itinerary position i (0 <= i < 5).
#   S[i]  : the arrival day at the city visited at position i.
#
# For the first city (i==0): the visit interval = [S[i], S[i] + duration - 1].
# For every subsequent city (i>=1): effective visit interval = [S[i], S[i] + duration - 2].
#
# The departure day from the final city must equal total_trip = 23.
# -----------------------------------------------------------------------------
n = 5
total_trip = 23
s = Solver()

# Permutation variable: each city appears exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector.
S = IntVector("S", n)
s.add(S[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions to compute durations at itinerary positions.
def full_duration(i):
    # For the first visited city (i==0).
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

def effective_duration(i):
    # For subsequent cities (i>=1): effective duration = (duration - 1).
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#    S[1] = S[0] + full_duration(0).
# For positions i >= 2:
#    S[i] = S[i-1] + effective_duration(i-1).
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the final city (position n-1), if not the first city then effective departure day is:
#   Departure = S[n-1] + (duration - 1) - 1 = S[n-1] + duration - 2.
# This must equal total_trip (23).
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair in the itinerary (positions i and i+1), there must be a direct flight.
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
# For each event city visited at itinerary position i, its visit interval must cover the event window.
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
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    
    # Compute the final trip end.
    last_city = itinerary[n-1]
    if n-1 == 0:
        final_departure = arrivals[n-1] + durations[last_city] - 1
    else:
        final_departure = arrivals[n-1] + durations[last_city] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")