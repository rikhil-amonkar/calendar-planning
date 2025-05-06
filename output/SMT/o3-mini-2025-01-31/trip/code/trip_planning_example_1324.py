from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 9 cities:
# 0: Venice      – 4 days.
# 1: Barcelona   – 3 days.
#                   Event: Meet a friend in Barcelona between day 10 and day 12.
# 2: Copenhagen  – 4 days.
#                   Event: Visit relatives in Copenhagen between day 7 and day 10.
# 3: Lyon        – 4 days.
# 4: Reykjavik   – 4 days.
# 5: Dubrovnik   – 5 days.
#                   Event: Attend a wedding in Dubrovnik between day 16 and day 20.
# 6: Athens      – 2 days.
# 7: Tallinn     – 5 days.
# 8: Munich      – 3 days.
#
# Total planned days = 4 + 3 + 4 + 4 + 4 + 5 + 2 + 5 + 3 = 34.
# There are 8 flights between 9 cities, so effective trip duration = 34 - 8 = 26 days.
#
# Note:
# - In the first city you enjoy its full planned duration.
# - In every subsequent city, one day is "lost" due to the flight (effective stay = duration - 1).
# -----------------------------------------------------------------------------
cities    = ["Venice", "Barcelona", "Copenhagen", "Lyon", "Reykjavik", "Dubrovnik", "Athens", "Tallinn", "Munich"]
durations = [4,         3,           4,           4,    4,           5,         2,       5,        3]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    1: (10, 12),  # Barcelona: Meet a friend between day 10 and day 12.
    2: (7, 10),   # Copenhagen: Visit relatives between day 7 and day 10.
    5: (16, 20)   # Dubrovnik: Wedding between day 16 and day 20.
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# The direct flights (with bidirectional pairs unless noted otherwise) are:
#
# - Copenhagen and Athens             -> (2,6) and (6,2)
# - Copenhagen and Dubrovnik          -> (2,5) and (5,2)
# - Munich and Tallinn                -> (8,7) and (7,8)
# - Copenhagen and Munich             -> (2,8) and (8,2)
# - Venice and Munich                 -> (0,8) and (8,0)
# - from Reykjavik to Athens (one-way)-> (4,6)
# - Athens and Dubrovnik              -> (6,5) and (5,6)
# - Venice and Athens                 -> (0,6) and (6,0)
# - Lyon and Barcelona                -> (3,1) and (1,3)
# - Copenhagen and Reykjavik          -> (2,4) and (4,2)
# - Reykjavik and Munich              -> (4,8) and (8,4)
# - Athens and Munich                 -> (6,8) and (8,6)
# - Lyon and Munich                   -> (3,8) and (8,3)
# - Barcelona and Reykjavik           -> (1,4) and (4,1)
# - Venice and Copenhagen             -> (0,2) and (2,0)
# - Barcelona and Dubrovnik           -> (1,5) and (5,1)
# - Lyon and Venice                   -> (3,0) and (0,3)
# - Dubrovnik and Munich              -> (5,8) and (8,5)
# - Barcelona and Athens              -> (1,6) and (6,1)
# - Copenhagen and Barcelona          -> (2,1) and (1,2)
# - Venice and Barcelona              -> (0,1) and (1,0)
# - Barcelona and Munich              -> (1,8) and (8,1)
# - Barcelona and Tallinn             -> (1,7) and (7,1)
# - Copenhagen and Tallinn            -> (2,7) and (7,2)
# -----------------------------------------------------------------------------
allowed_flights = {
    (2,6), (6,2),
    (2,5), (5,2),
    (8,7), (7,8),
    (2,8), (8,2),
    (0,8), (8,0),
    (4,6),         # one-way from Reykjavik to Athens
    (6,5), (5,6),
    (0,6), (6,0),
    (3,1), (1,3),
    (2,4), (4,2),
    (4,8), (8,4),
    (6,8), (8,6),
    (3,8), (8,3),
    (1,4), (4,1),
    (0,2), (2,0),
    (1,5), (5,1),
    (3,0), (0,3),
    (5,8), (8,5),
    (1,6), (6,1),
    (2,1), (1,2),
    (0,1), (1,0),
    (1,8), (8,1),
    (1,7), (7,1),
    (2,7), (7,2)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation (ordering) of the 9 cities:
#   pos[i] : the city index visited at itinerary position i, (0 <= i < 9).
#   S[i]   : the arrival day at the city visited at position i.
#
# For the first city (i==0): visit interval = [S[i], S[i] + duration - 1].
# For every subsequent city (i>=1): effective visit interval
#         = [S[i], S[i] + duration - 2]  (losing one day to the flight).
#
# The departure day from the final city must equal total_trip = 26.
# -----------------------------------------------------------------------------
n = 9
total_trip = 26
s = Solver()

# Permutation variable: each city must be visited exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector.
S = IntVector("S", n)
s.add(S[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions for duration expressions:
def full_duration(i):
    # For the first visited city, full planned duration.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

def effective_duration(i):
    # For subsequent cities, effective duration = (duration - 1).
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#    S[1] = S[0] + [full duration of city at pos[0]].
# For positions i >= 2:
#    S[i] = S[i-1] + [effective duration of city at pos[i-1]].
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the final city (position n-1), if not the first city then its departure day is:
#    Departure = S[n-1] + (duration - 1) - 1 = S[n-1] + duration - 2.
# This must equal total_trip (26).
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair of itinerary positions (i and i+1),
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
# For any city with an event, if that city is visited at itinerary position i,
# then its visit interval must cover the event window.
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
        city_index = itinerary[i]
        city_name = cities[city_index]
        if i == 0:
            departure = arrivals[i] + durations[city_index] - 1
        else:
            departure = arrivals[i] + durations[city_index] - 2
        print(f" Position {i+1}: {city_name:12s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    
    # Compute final trip end day.
    last_city = itinerary[-1]
    if n - 1 == 0:
        final_departure = arrivals[-1] + durations[last_city] - 1
    else:
        final_departure = arrivals[-1] + durations[last_city] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")