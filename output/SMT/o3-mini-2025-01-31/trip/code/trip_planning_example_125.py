from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 3 cities:
# 0: Stuttgart – 6 days.
#             Event: Meet a friend in Stuttgart between day 1 and day 6.
# 1: Seville   – 7 days.
# 2: Manchester– 4 days.
#
# Total planned days = 6 + 7 + 4 = 17.
# There are 2 flights between cities, so the effective trip duration becomes
# 17 - 2 = 15 days.
#
# Note:
# - In the first visited city, you use the full planned duration.
# - For every subsequent city, one day is lost due to a flight, so the effective
#   duration is (duration - 1).
# -----------------------------------------------------------------------------
cities    = ["Stuttgart", "Seville", "Manchester"]
durations = [6,           7,         4]

# Event for Stuttgart (city index 0): must cover the window [1, 6].
events = {
    0: (1, 6)
}

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional):
#
# - Manchester and Seville        -> (Manchester, Seville) and (Seville, Manchester)
# - Stuttgart and Manchester      -> (Stuttgart, Manchester) and (Manchester, Stuttgart)
#
# Note: There is no direct flight between Stuttgart and Seville.
# -----------------------------------------------------------------------------
allowed_flights = {
    (0, 2), (2, 0),  # Stuttgart <-> Manchester
    (2, 1), (1, 2)   # Manchester <-> Seville
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# The itinerary is represented as a permutation of the 3 cities:
#   pos[i] : the city index visited at itinerary position i (i=0,1,2).
#   S[i]   : the arrival day at the city in position i.
#
# For the first city (i == 0):
#   Visit interval = [S[0], S[0] + durations - 1].
# For each subsequent city (i >= 1):
#   Visit interval = [S[i], S[i] + (duration - 1) - 0] 
#   (i.e. effectively, [S[i], S[i]+duration-2]).
#
# Final constraint: Departure day from the last city equals total_trip = 15.
# -----------------------------------------------------------------------------
n = 3
total_trip = 15
s = Solver()

# Permutation: each city appears exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival day for each visited city.
S = IntVector("S", n)
s.add(S[0] == 1)  # The trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions to compute durations based on the itinerary position:
def full_duration(i):
    # For the first visited city, use the full planned duration.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])
    
def effective_duration(i):
    # For subsequent cities, effective duration = planned duration - 1.
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For the second city (i == 1):
#   S[1] = S[0] + (full duration of city at pos[0]).
# For positions i >= 2:
#   S[i] = S[i-1] + (effective duration of city at pos[i-1]).
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# The departure day from the final city is:
#   If first city: S[n-1] + duration - 1
#   Otherwise:    S[n-1] + (duration - 1) - 1  which simplifies to S[n-1] + duration - 2.
#
# We impose:
#   S[n-1] + effective_duration(n-1) - 1 == total_trip
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every pair of consecutive cities, there must be a direct flight.
# -----------------------------------------------------------------------------
for i in range(n - 1):
    valid_flights = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                valid_flights.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(valid_flights))

# -----------------------------------------------------------------------------
# Event constraints:
#
# For each event city, if it is visited at itinerary position i,
# then its visit interval must cover the event window.
#
# The visit interval is:
#   - For the first city (i == 0): [S[i], S[i] + durations[city] - 1].
#   - For subsequent cities (i >= 1): [S[i], S[i] + durations[city] - 2].
#
# For Stuttgart (city 0): event window is [1, 6].
# -----------------------------------------------------------------------------
for i in range(n):
    for city, (event_start, event_end) in events.items():
        s.add(
            If(pos[i] == city,
               And(
                   S[i] <= event_start,
                   If(i == 0,
                      S[i] + durations[city] - 1 >= event_end,
                      S[i] + durations[city] - 2 >= event_end)
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
        print(f" Position {i+1}: {city_name:12s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    
    # Final trip end day:
    if n - 1 == 0:
        final_departure = arrivals[-1] + durations[itinerary[-1]] - 1
    else:
        final_departure = arrivals[-1] + durations[itinerary[-1]] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")