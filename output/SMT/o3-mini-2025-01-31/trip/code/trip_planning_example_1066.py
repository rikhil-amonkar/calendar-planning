from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 8 cities:
# 0: Brussels  – 4 days.
# 1: Bucharest – 3 days.
# 2: Stuttgart – 4 days.
#              Event: Meet a friend in Stuttgart between day 1 and day 4.
# 3: Mykonos   – 2 days.
# 4: Madrid    – 2 days.
#              Event: Attend a conference in Madrid during day 20 and day 21.
# 5: Helsinki  – 5 days.
# 6: Split     – 3 days.
# 7: London    – 5 days.
#
# Planned total days = 4 + 3 + 4 + 2 + 2 + 5 + 3 + 5 = 28 days.
# There are 7 intercity flights, so effective trip duration = 28 - 7 = 21 days.
#
# Note:
# - The first visited city is used in full, i.e. its visit interval is 
#   [arrival_day, arrival_day + duration - 1].
# - For every subsequent city, one day is "lost" to the flight, so the effective 
#   visit interval is [arrival_day, arrival_day + duration - 2].
# -----------------------------------------------------------------------------
cities    = ["Brussels", "Bucharest", "Stuttgart", "Mykonos", "Madrid", "Helsinki", "Split", "London"]
durations = [4,          3,         4,         2,        2,       5,         3,      5]

# Events:
# Stuttgart (city 2): meet friend event, need to cover days 1 to 4.
# Madrid (city 4): conference event, need to cover days 20 to 21.
events = {
    2: (1, 4),
    4: (20, 21)
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# Provided flights (bidirectional):
# - Helsinki and London     -> (5,7) and (7,5)
# - Split and Madrid         -> (6,4) and (4,6)
# - Helsinki and Madrid      -> (5,4) and (4,5)
# - London and Madrid        -> (7,4) and (4,7)
# - Brussels and London      -> (0,7) and (7,0)
# - Bucharest and London     -> (1,7) and (7,1)
# - Brussels and Bucharest   -> (0,1) and (1,0)
# - Bucharest and Madrid     -> (1,4) and (4,1)
# - Split and Helsinki       -> (6,5) and (5,6)
# - Mykonos and Madrid       -> (3,4) and (4,3)
# - Stuttgart and London     -> (2,7) and (7,2)
# - Helsinki and Brussels    -> (5,0) and (0,5)
# - Brussels and Madrid      -> (0,4) and (4,0)
# - Split and London         -> (6,7) and (7,6)
# - Stuttgart and Split      -> (2,6) and (6,2)
# - London and Mykonos       -> (7,3) and (3,7)
# -----------------------------------------------------------------------------
allowed_flights = {
    (5, 7), (7, 5),
    (6, 4), (4, 6),
    (5, 4), (4, 5),
    (7, 4), (4, 7),
    (0, 7), (7, 0),
    (1, 7), (7, 1),
    (0, 1), (1, 0),
    (1, 4), (4, 1),
    (6, 5), (5, 6),
    (3, 4), (4, 3),
    (2, 7), (7, 2),
    (5, 0), (0, 5),
    (0, 4), (4, 0),
    (6, 7), (7, 6),
    (2, 6), (6, 2),
    (7, 3), (3, 7)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation of the 8 cities:
#   pos[i] : the city index visited at itinerary position i (for i in 0..7).
#   S[i]   : the arrival day at the city in position i.
#
# For the first visited city (i == 0): visit interval = [S[i], S[i] + duration - 1].
# For any subsequent city (i >= 1): visit interval = [S[i], S[i] + duration - 2].
#
# The trip ends when, for the final city at position n-1, we have:
#   S[n-1] + effective_duration(n-1) - 1 == total_trip,
# where effective_duration for i>=1 is (duration - 1).
# -----------------------------------------------------------------------------
n = 8
total_trip = 21
s = Solver()

# Permutation variable for the order of cities.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days for each city. Trip starts at day 1.
S = IntVector("S", n)
s.add(S[0] == 1)
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions for durations.
def full_duration(i):
    # For the first city use full planned duration.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

def effective_duration(i):
    # For subsequent cities, effective duration = planned duration - 1.
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For the second city (i == 1):
#   S[1] = S[0] + full_duration(0)
# For cities i >= 2:
#   S[i] = S[i-1] + effective_duration(i-1)
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i - 1))

# -----------------------------------------------------------------------------
# Final trip end constraint:
#
# For the final city at position n-1 (which is not first):
#   Departure day = S[n-1] + (duration - 1) - 1 = S[n-1] + duration - 2.
# We require:
#   S[n-1] + effective_duration(n-1) - 1 == total_trip
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Direct flight connectivity constraints:
#
# For every consecutive pair (i, i+1) in the itinerary, there must be a direct flight.
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
# For each event city, if the city is visited at position i,
# then its visit interval must cover the event window.
# Visit interval definitions:
#   If i == 0: Interval = [S[i], S[i] + duration - 1]
#   If i >= 1: Interval = [S[i], S[i] + duration - 2]
#
# Stuttgart (city 2): require interval covers [1, 4].
# Madrid (city 4): require interval covers [20, 21].
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
    
    if n - 1 == 0:
        final_departure = arrivals[-1] + durations[itinerary[-1]] - 1
    else:
        final_departure = arrivals[-1] + durations[itinerary[-1]] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")