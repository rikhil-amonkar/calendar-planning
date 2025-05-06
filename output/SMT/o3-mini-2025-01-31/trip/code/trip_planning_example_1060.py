from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 8 cities:
# 0: Stuttgart  – 4 days.
#      Event: Attend a conference in Stuttgart between day 4 and day 7.
# 1: Istanbul   – 4 days.
#      Event: Visit relatives in Istanbul between day 19 and day 22.
# 2: Vilnius    – 4 days.
# 3: Seville    – 3 days.
# 4: Geneva     – 5 days.
# 5: Valencia   – 5 days.
# 6: Munich     – 3 days.
#      Event: Annual show in Munich from day 13 to day 15.
# 7: Reykjavik  – 4 days.
#      Event: Attend a workshop in Reykjavik between day 1 and day 4.
#
# Total planned days = 4 + 4 + 4 + 3 + 5 + 5 + 3 + 4 = 32.
# There are 7 flights (transitions), so the effective trip duration = 32 - 7 = 25 days.
#
# Note:
# - In the first city you use its full planned duration.
# - In every subsequent city, one day is lost for the flight, so effective duration = (duration - 1).
# -----------------------------------------------------------------------------
cities    = ["Stuttgart", "Istanbul", "Vilnius", "Seville", "Geneva", "Valencia", "Munich", "Reykjavik"]
durations = [4,           4,          4,        3,        5,       5,         3,       4]

# Event windows (city index -> (event_start, event_end))
events = {
    0: (4, 7),   # Stuttgart: conference between day 4 and day 7.
    1: (19, 22), # Istanbul: visit relatives between day 19 and day 22.
    6: (13, 15), # Munich: annual show between day 13 and day 15.
    7: (1, 4)    # Reykjavik: workshop between day 1 and day 4.
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# The flights (with one-way flights indicated) are:
# - Geneva and Istanbul            : (4,1) and (1,4)
# - Reykjavik and Munich             : (7,6) and (6,7)
# - Stuttgart and Valencia           : (0,5) and (5,0)
# - from Reykjavik to Stuttgart      : (7,0)
# - Stuttgart and Istanbul           : (0,1) and (1,0)
# - Munich and Geneva                : (6,4) and (4,6)
# - Istanbul and Vilnius             : (1,2) and (2,1)
# - Valencia and Seville             : (5,3) and (3,5)
# - Valencia and Istanbul            : (5,1) and (1,5)
# - from Vilnius to Munich           : (2,6)
# - Seville and Munich               : (3,6) and (6,3)
# - Munich and Istanbul              : (6,1) and (1,6)
# - Valencia and Geneva              : (5,4) and (4,5)
# - Valencia and Munich              : (5,6) and (6,5)
# -----------------------------------------------------------------------------
allowed_flights = {
    (4,1), (1,4),
    (7,6), (6,7),
    (0,5), (5,0),
    (7,0),      # one-way: Reykjavik -> Stuttgart
    (0,1), (1,0),
    (6,4), (4,6),
    (1,2), (2,1),
    (5,3), (3,5),
    (5,1), (1,5),
    (2,6),      # one-way: Vilnius -> Munich
    (3,6), (6,3),
    (6,1), (1,6),
    (5,4), (4,5),
    (5,6), (6,5)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation (ordering) of the 8 cities:
#   pos[i] : the city index visited at itinerary position i (for 0 <= i < 8).
#   S[i]   : the arrival day at the city visited at position i.
#
# For the first city (i == 0): the visit interval is [S[i], S[i] + duration - 1].
# For every subsequent city (i >= 1): effective visit interval is [S[i], S[i] + duration - 2].
#
# The departure day from the final city must equal total_trip = 25.
# -----------------------------------------------------------------------------
n = 8
total_trip = 25
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

# Helper functions for duration at itinerary positions.
def full_duration(i):
    # For the first visited city, use the full planned duration.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

def effective_duration(i):
    # For subsequent cities, effective duration is (duration - 1).
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#   S[1] = S[0] + (full duration of the city at pos[0]).
# For positions i >= 2:
#   S[i] = S[i-1] + (effective duration of the city at pos[i-1]).
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the final city (position n-1), the departure day is:
#   If i==0: S[n-1] + duration - 1,
#   else: S[n-1] + duration - 2.
# This must equal total_trip (25).
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair in the itinerary (positions i and i+1),
# there must be a direct flight between the cities.
# -----------------------------------------------------------------------------
for i in range(n-1):
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
# then its visit interval must cover the event window.
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
    
    # Compute the final trip end day.
    last_city = itinerary[-1]
    if n - 1 == 0:
        final_departure = arrivals[-1] + durations[last_city] - 1
    else:
        final_departure = arrivals[-1] + durations[last_city] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")