from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 10 cities:
# 0: Stockholm  – 3 days.
# 1: Hamburg    – 5 days.
# 2: Florence   – 2 days.
# 3: Istanbul   – 5 days.
#                Event: Attend annual show in Istanbul between day 25 and day 29.
# 4: Oslo       – 5 days.
# 5: Vilnius    – 5 days.
# 6: Santorini  – 2 days.
# 7: Munich     – 5 days.
# 8: Frankfurt  – 4 days.
# 9: Krakow     – 5 days.
#                Event: Attend workshop in Krakow between day 5 and day 9.
#
# Total planned days = 3+5+2+5+5+5+2+5+4+5 = 41 days.
# There are 9 flights between cities, so effective trip duration = 41 - 9 = 32 days.
#
# Note:
# - In the first city, the full planned duration is used.
# - In every subsequent city, one day is lost for the flight,
#   so effective duration = (duration - 1).
# -----------------------------------------------------------------------------
cities    = ["Stockholm", "Hamburg", "Florence", "Istanbul", "Oslo", 
             "Vilnius", "Santorini", "Munich", "Frankfurt", "Krakow"]
durations = [3,           5,         2,         5,         5, 
             5,           2,         5,         4,         5]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    3: (25, 29),  # Istanbul event: annual show
    9: (5, 9)     # Krakow event: workshop
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# The flights below are the given direct flights, with one-way flights indicated.
#
# - Oslo and Stockholm           -> bidirectional: (Oslo,Stockholm) and (Stockholm,Oslo)
#     Oslo (4), Stockholm (0)
# - Krakow and Frankfurt         -> bidirectional: (Krakow,Frankfurt) and (Frankfurt,Krakow)
#     Krakow (9), Frankfurt (8)
# - Krakow and Istanbul          -> bidirectional: (Krakow,Istanbul) and (Istanbul,Krakow)
#     Krakow (9), Istanbul (3)
# - Munich and Stockholm         -> bidirectional: (Munich,Stockholm) and (Stockholm, Munich)
#     Munich (7), Stockholm (0)
# - Hamburg and Stockholm        -> bidirectional: (Hamburg,Stockholm) and (Stockholm,Hamburg)
#     Hamburg (1), Stockholm (0)
# - from Krakow to Vilnius       -> one-way only: (Krakow, Vilnius)
#     Krakow (9) -> Vilnius (5)
# - Oslo and Istanbul            -> bidirectional: (Oslo,Istanbul) and (Istanbul,Oslo)
#     Oslo (4), Istanbul (3)
# - Istanbul and Stockholm       -> bidirectional: (Istanbul,Stockholm) and (Stockholm,Istanbul)
#     Istanbul (3), Stockholm (0)
# - Oslo and Krakow              -> bidirectional: (Oslo, Krakow) and (Krakow,Oslo)
#     Oslo (4), Krakow (9)
# - Vilnius and Istanbul         -> bidirectional: (Vilnius,Istanbul) and (Istanbul, Vilnius)
#     Vilnius (5), Istanbul (3)
# - Oslo and Vilnius             -> bidirectional: (Oslo, Vilnius) and (Vilnius,Oslo)
#     Oslo (4), Vilnius (5)
# - Frankfurt and Istanbul       -> bidirectional: (Frankfurt,Istanbul) and (Istanbul,Frankfurt)
#     Frankfurt (8), Istanbul (3)
# - Oslo and Frankfurt           -> bidirectional: (Oslo,Frankfurt) and (Frankfurt,Oslo)
#     Oslo (4), Frankfurt (8)
# - Munich and Hamburg           -> bidirectional: (Munich,Hamburg) and (Hamburg,Munich)
#     Munich (7), Hamburg (1)
# - Munich and Istanbul          -> bidirectional: (Munich,Istanbul) and (Istanbul, Munich)
#     Munich (7), Istanbul (3)
# - Oslo and Munich              -> bidirectional: (Oslo, Munich) and (Munich, Oslo)
#     Oslo (4), Munich (7)
# - Frankfurt and Florence       -> bidirectional: (Frankfurt,Florence) and (Florence,Frankfurt)
#     Frankfurt (8), Florence (2)
# - Oslo and Hamburg             -> bidirectional: (Oslo,Hamburg) and (Hamburg,Oslo)
#     Oslo (4), Hamburg (1)
# - Vilnius and Frankfurt        -> bidirectional: (Vilnius,Frankfurt) and (Frankfurt, Vilnius)
#     Vilnius (5), Frankfurt (8)
# - from Florence to Munich      -> one-way only: (Florence, Munich)
#     Florence (2) -> Munich (7)
# - Krakow and Munich            -> bidirectional: (Krakow, Munich) and (Munich, Krakow)
#     Krakow (9), Munich (7)
# - Hamburg and Istanbul         -> bidirectional: (Hamburg,Istanbul) and (Istanbul,Hamburg)
#     Hamburg (1), Istanbul (3)
# - Frankfurt and Stockholm      -> bidirectional: (Frankfurt,Stockholm) and (Stockholm,Frankfurt)
#     Frankfurt (8), Stockholm (0)
# - from Stockholm to Santorini  -> one-way only: (Stockholm, Santorini)
#     Stockholm (0) -> Santorini (6)
# - Frankfurt and Munich         -> bidirectional: (Frankfurt, Munich) and (Munich,Frankfurt)
#     Frankfurt (8), Munich (7)
# - from Santorini to Oslo       -> one-way only: (Santorini, Oslo)
#     Santorini (6) -> Oslo (4)
# - Krakow and Stockholm         -> bidirectional: (Krakow,Stockholm) and (Stockholm,Krakow)
#     Krakow (9), Stockholm (0)
# - from Vilnius to Munich       -> one-way only: (Vilnius, Munich)
#     Vilnius (5) -> Munich (7)
# - Frankfurt and Hamburg        -> bidirectional: (Frankfurt,Hamburg) and (Hamburg,Frankfurt)
#     Frankfurt (8), Hamburg (1)
# -----------------------------------------------------------------------------
allowed_flights = {
    (4,0), (0,4),                     # Oslo - Stockholm
    (9,8), (8,9),                     # Krakow - Frankfurt
    (9,3), (3,9),                     # Krakow - Istanbul
    (7,0), (0,7),                     # Munich - Stockholm
    (1,0), (0,1),                     # Hamburg - Stockholm
    (9,5),                           # from Krakow to Vilnius (one-way)
    (4,3), (3,4),                     # Oslo - Istanbul
    (3,0), (0,3),                     # Istanbul - Stockholm
    (4,9), (9,4),                     # Oslo - Krakow
    (5,3), (3,5),                     # Vilnius - Istanbul
    (4,5), (5,4),                     # Oslo - Vilnius
    (8,3), (3,8),                     # Frankfurt - Istanbul
    (4,8), (8,4),                     # Oslo - Frankfurt
    (7,1), (1,7),                     # Munich - Hamburg
    (7,3), (3,7),                     # Munich - Istanbul
    (4,7), (7,4),                     # Oslo - Munich
    (8,2), (2,8),                     # Frankfurt - Florence
    (4,1), (1,4),                     # Oslo - Hamburg
    (5,8), (8,5),                     # Vilnius - Frankfurt
    (2,7),                           # from Florence to Munich (one-way)
    (9,7), (7,9),                     # Krakow - Munich
    (1,3), (3,1),                     # Hamburg - Istanbul
    (8,0), (0,8),                     # Frankfurt - Stockholm
    (0,6),                           # from Stockholm to Santorini (one-way)
    (8,7), (7,8),                     # Frankfurt - Munich
    (6,4),                           # from Santorini to Oslo (one-way)
    (9,0), (0,9),                     # Krakow - Stockholm
    (5,7),                           # from Vilnius to Munich (one-way)
    (8,1), (1,8)                      # Frankfurt - Hamburg
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation (ordering) of the 10 cities:
#   pos[i] : the city index visited at itinerary position i, where 0<=i<10.
#   S[i]   : the arrival day at the city visited at position i.
#
# For the first city (i==0), the visit interval = [S[i], S[i]+duration - 1].
# For every subsequent city (i>=1), the effective visit interval = [S[i], S[i]+duration - 2].
#
# The departure day from the final city must equal total_trip = 32.
# -----------------------------------------------------------------------------
n = 10
total_trip = 32
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

# Helper functions for duration expressions.
def full_duration(i):
    # For the first visited city, use its full planned duration.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

def effective_duration(i):
    # For subsequent cities, effective duration = (duration - 1).
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#    S[1] = S[0] + (full duration of city at pos[0]).
# For positions i >= 2:
#    S[i] = S[i-1] + (effective duration of city at pos[i-1]).
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the final city (position n-1), if not the first city then its departure day is:
#    Departure = S[n-1] + (duration - 1) - 1 = S[n-1] + duration - 2.
# This must equal total_trip (32).
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair of itinerary positions (i and i+1),
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
# For each city with an event, if visited at itinerary position i,
# the visit interval must cover the event window.
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
    
    # Compute final trip end.
    last_city = itinerary[-1]
    if n - 1 == 0:
        final_departure = arrivals[-1] + durations[last_city] - 1
    else:
        final_departure = arrivals[-1] + durations[last_city] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")