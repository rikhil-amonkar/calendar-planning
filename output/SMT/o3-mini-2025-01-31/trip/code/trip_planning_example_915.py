from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 7 cities:
# 0: Bucharest – 3 days.
# 1: Venice    – 5 days.
#              Event: Attend a wedding in Venice between day 22 and day 26.
# 2: Prague   – 4 days.
# 3: Frankfurt– 5 days.
#              Event: Annual show in Frankfurt between day 12 and day 16.
# 4: Zurich   – 5 days.
# 5: Florence – 5 days.
# 6: Tallinn  – 5 days.
#              Event: Meet friends in Tallinn between day 8 and day 12.
#
# Planned total days = 3 + 5 + 4 + 5 + 5 + 5 + 5 = 32.
# There are 6 flights (7 cities visited in sequence),
# so the effective trip duration = 32 - 6 = 26 days.
#
# Note:
# - For the first visited city, the visit interval is [arrival, arrival + duration - 1].
# - For every subsequent city, one day is lost for commuting,
#   so the effective visit interval is [arrival, arrival + duration - 2].
# -----------------------------------------------------------------------------
cities    = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]
durations = [3,           5,       4,       5,         5,       5,         5]

# Event windows:
# Venice (city 1): wedding from day 22 to day 26.
# Frankfurt (city 3): annual show from day 12 to day 16.
# Tallinn (city 6): meet friends event from day 8 to day 12.
events = {
    1: (22, 26),
    3: (12, 16),
    6: (8, 12)
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# Provided flights (note: most flights are bidirectional except "from Zurich to Florence" 
# which is unidirectional, from Zurich to Florence only):
#
# - Prague and Tallinn           -> (2,6) and (6,2)
# - Prague and Zurich            -> (2,4) and (4,2)
# - Florence and Prague          -> (5,2) and (2,5)
# - Frankfurt and Bucharest      -> (3,0) and (0,3)
# - Frankfurt and Venice         -> (3,1) and (1,3)
# - Prague and Bucharest         -> (2,0) and (0,2)
# - Bucharest and Zurich         -> (0,4) and (4,0)
# - Tallinn and Frankfurt        -> (6,3) and (3,6)
# - from Zurich to Florence      -> (4,5) only (not the reverse)
# - Frankfurt and Zurich         -> (3,4) and (4,3)
# - Zurich and Venice            -> (4,1) and (1,4)
# - Florence and Frankfurt       -> (5,3) and (3,5)
# - Prague and Frankfurt         -> (2,3) and (3,2)
# - Tallinn and Zurich           -> (6,4) and (4,6)
# -----------------------------------------------------------------------------
allowed_flights = {
    (2, 6), (6, 2),
    (2, 4), (4, 2),
    (5, 2), (2, 5),
    (3, 0), (0, 3),
    (3, 1), (1, 3),
    (2, 0), (0, 2),
    (0, 4), (4, 0),
    (6, 3), (3, 6),
    (4, 5),       # Unidirectional: from Zurich (4) to Florence (5)
    (3, 4), (4, 3),
    (4, 1), (1, 4),
    (5, 3), (3, 5),
    (2, 3), (3, 2),
    (6, 4), (4, 6)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation of the 7 cities:
#   pos[i] : the city index visited at itinerary position i, for i in 0..6.
#   S[i]   : the arrival day at the city in position i.
#
# For the first city (i == 0): Visit interval = [S[0], S[0] + durations - 1].
# For each subsequent city (i >= 1): Visit interval = [S[i], S[i] + durations - 2].
#
# The departure from the final city is constrained such that
#   S[n-1] + effective_duration(n-1) - 1 == total_trip
# (where for subsequent cities, effective_duration = planned duration - 1).
# -----------------------------------------------------------------------------
n = 7
total_trip = 26
s = Solver()

# Ensure permutation: each city appears exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival day for each visited city.
S = IntVector("S", n)
s.add(S[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions to compute durations based on itinerary position:
def full_duration(i):
    # For the first city, planned duration is used in full.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

def effective_duration(i):
    # For subsequent cities, effective duration = planned duration - 1.
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1 (the second visited city):
#   S[1] = S[0] + (full duration of city at pos[0]).
# For positions 2 to n-1:
#   S[i] = S[i-1] + (effective_duration of city at pos[i-1]).
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))

# -----------------------------------------------------------------------------
# Final trip constraint:
#
# The departure day from the final city is calculated as:
#   For first city: departure = S[0] + durations - 1.
#   For any other city: departure = S[i] + durations - 2.
#
# We impose:
#   S[n-1] + effective_duration(n-1) - 1 == total_trip
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Direct flight connectivity constraints:
#
# For every consecutive pair of cities in the itinerary,
# there must be a direct flight (respecting allowed directions).
# -----------------------------------------------------------------------------
for i in range(n - 1):
    possible_flights = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                possible_flights.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(possible_flights))

# -----------------------------------------------------------------------------
# Event constraints:
#
# For each city with an event: if that city is visited at itinerary position i,
# then its visit interval must cover the event window.
#
# Visit interval definition:
# - For the first city (i==0): [S[i], S[i] + durations - 1].
# - For subsequent cities (i>=1): [S[i], S[i] + durations - 2].
#
# Apply event constraints for:
#   Venice (city 1): wedding from day 22 to day 26.
#   Frankfurt (city 3): show from day 12 to day 16.
#   Tallinn (city 6): friends meeting from day 8 to day 12.
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
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    
    # Compute trip end day for final city
    if n-1 == 0:
        final_departure = arrivals[-1] + durations[itinerary[-1]] - 1
    else:
        final_departure = arrivals[-1] + durations[itinerary[-1]] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")