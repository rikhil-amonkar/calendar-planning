from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 5 cities:
# 0: Stuttgart – 2 days.
# 1: Bucharest – 2 days.
# 2: Geneva    – 4 days.
#              Event: Visit relatives in Geneva between day 1 and day 4.
# 3: Valencia  – 6 days.
# 4: Munich    – 7 days.
#              Event: Meet friends in Munich between day 4 and day 10.
#
# Total planned days = 2 + 2 + 4 + 6 + 7 = 21.
# There are 4 flight transitions (since 5 cities), so effective trip duration = 21 - 4 = 17 days.
#
# Note:
# - In the first visited city you get the full planned duration.
# - For every subsequent city you lose one day due to flying, so the effective duration = duration - 1.
# -----------------------------------------------------------------------------
cities    = ["Stuttgart", "Bucharest", "Geneva", "Valencia", "Munich"]
durations = [2,           2,         4,       6,         7]

# Event windows:
# For Geneva (index 2): the visit interval must cover from day 1 to day 4.
# For Munich (index 4): the visit interval must cover from day 4 to day 10.
events = {
    2: (1, 4),
    4: (4, 10)
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# Provided flights (bidirectional):
# - Geneva and Munich        -> (2,4) and (4,2)
# - Munich and Valencia      -> (4,3) and (3,4)
# - Bucharest and Valencia   -> (1,3) and (3,1)
# - Munich and Bucharest     -> (4,1) and (1,4)
# - Valencia and Stuttgart   -> (3,0) and (0,3)
# - Geneva and Valencia      -> (2,3) and (3,2)
# -----------------------------------------------------------------------------
allowed_flights = {
    (2,4), (4,2),
    (4,3), (3,4),
    (1,3), (3,1),
    (4,1), (1,4),
    (3,0), (0,3),
    (2,3), (3,2)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation of the 5 cities:
#   pos[i] : the city index visited at itinerary position i (i = 0,...,4).
#   S[i]   : the arrival day at the city visited at position i.
#
# For the first city (i == 0): the visit interval is [S[0], S[0] + durations - 1].
# For every subsequent city (i >= 1): the effective visit interval is [S[i], S[i] + (duration - 1) - 1]
#   i.e., [S[i], S[i] + durations - 2].
#
# The departure day from the final city must equal total_trip = 17.
# -----------------------------------------------------------------------------
n = 5
total_trip = 17
s = Solver()

# Permutation constraint: each city appears exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days for each city.
S = IntVector("S", n)
s.add(S[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions to compute durations:
# For the first visited city, we use the full planned duration.
def full_duration(i):
    # equals durations[city] for the city scheduled at pos[i]
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])
    
# For every subsequent city, effective duration = duration - 1.
def effective_duration(i):
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For the second city (i == 1):
#    S[1] = S[0] + (full duration of city at pos[0]).
# For positions 2 to n-1 (i >= 2):
#    S[i] = S[i-1] + (effective duration of city at pos[i-1]).
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i - 1))

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# The departure day from the final city is computed as follows:
# - If the final city is the first city (i==0): departure = S[0] + durations - 1.
# - Otherwise (i>=1): departure = S[n-1] + (duration - 1) - 1 = S[n-1] + duration - 2.
#
# Since n=5 > 1 here, we impose:
#   S[n-1] + effective_duration(n-1) - 1 == total_trip
# (where effective_duration(n-1) = durations[city]-1).
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every pair of consecutive cities in the itinerary, there must be a direct flight.
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
# For each event city, if that city is visited at itinerary position i then
# the visit interval must cover the event window.
#
# The visit interval is:
#  - If i == 0 (first city): [S[i], S[i] + durations - 1]
#  - If i >= 1: [S[i], S[i] + durations - 2]
#
# For Geneva (index 2): event window [1, 4].
# For Munich (index 4): event window [4, 10].
# -----------------------------------------------------------------------------
for i in range(n):
    for city, (event_lower, event_upper) in events.items():
        s.add(
            If(pos[i] == city,
               And(
                   S[i] <= event_lower,
                   If(i == 0,
                      S[i] + durations[city] - 1 >= event_upper,
                      S[i] + durations[city] - 2 >= event_upper)
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
    
    if n-1 == 0:
        final_departure = arrivals[-1] + durations[itinerary[-1]] - 1
    else:
        final_departure = arrivals[-1] + durations[itinerary[-1]] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")