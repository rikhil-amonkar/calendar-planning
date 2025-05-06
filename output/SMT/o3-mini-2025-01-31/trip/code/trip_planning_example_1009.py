from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 8 cities (indices in order):
# 0: Riga       – 4 days.
# 1: Manchester – 5 days.
# 2: Bucharest  – 4 days.
#                 Event: Workshop in Bucharest between day 16 and day 19.
# 3: Florence   – 4 days.
# 4: Vienna     – 2 days.
# 5: Istanbul   – 2 days.
#                 Event: Annual show in Istanbul between day 12 and day 13.
# 6: Reykjavik  – 4 days.
# 7: Stuttgart  – 5 days.
#
# Total planned days = 4 + 5 + 4 + 4 + 2 + 2 + 4 + 5 = 30 days.
# There are 7 flight transitions, so effective trip duration = 30 - 7 = 23 days.
#
# Note:
# - The trip starts on day 1 in the first city (enjoying its full duration).
# - In every subsequent city, one day is lost due to the flight (effective stay = duration - 1).
# -----------------------------------------------------------------------------
cities    = ["Riga", "Manchester", "Bucharest", "Florence", "Vienna", "Istanbul", "Reykjavik", "Stuttgart"]
durations = [4,      5,           4,          4,         2,       2,         4,          5]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    2: (16, 19),  # Bucharest: Workshop between day 16 and day 19.
    5: (12, 13)   # Istanbul: Annual show between day 12 and day 13.
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# Flights are specified as pairs (a, b) meaning a flight from city a to city b.
# All flights are bidirectional unless noted otherwise.
#
# 1. Bucharest and Vienna      -> (Bucharest, Vienna) and (Vienna, Bucharest)        -> (2,4) and (4,2)
# 2. Reykjavik and Vienna      -> (Reykjavik, Vienna) and (Vienna, Reykjavik)        -> (6,4) and (4,6)
# 3. Manchester and Vienna     -> (Manchester, Vienna) and (Vienna, Manchester)      -> (1,4) and (4,1)
# 4. Manchester and Riga       -> (Manchester, Riga) and (Riga, Manchester)          -> (1,0) and (0,1)
# 5. Riga and Vienna           -> (Riga, Vienna) and (Vienna, Riga)                  -> (0,4) and (4,0)
# 6. Istanbul and Vienna       -> (Istanbul, Vienna) and (Vienna, Istanbul)          -> (5,4) and (4,5)
# 7. Vienna and Florence       -> (Vienna, Florence) and (Florence, Vienna)          -> (4,3) and (3,4)
# 8. Stuttgart and Vienna      -> (Stuttgart, Vienna) and (Vienna, Stuttgart)        -> (7,4) and (4,7)
# 9. Riga and Bucharest        -> (Riga, Bucharest) and (Bucharest, Riga)            -> (0,2) and (2,0)
# 10. Istanbul and Riga        -> (Istanbul, Riga) and (Riga, Istanbul)              -> (5,0) and (0,5)
# 11. Stuttgart and Istanbul   -> (Stuttgart, Istanbul) and (Istanbul, Stuttgart)    -> (7,5) and (5,7)
# 12. From Reykjavik to Stuttgart -> one-way only: (Reykjavik, Stuttgart)           -> (6,7)
# 13. Istanbul and Bucharest   -> (Istanbul, Bucharest) and (Bucharest, Istanbul)    -> (5,2) and (2,5)
# 14. Manchester and Istanbul  -> (Manchester, Istanbul) and (Istanbul, Manchester)  -> (1,5) and (5,1)
# 15. Manchester and Bucharest -> (Manchester, Bucharest) and (Bucharest, Manchester)-> (1,2) and (2,1)
# 16. Stuttgart and Manchester -> (Stuttgart, Manchester) and (Manchester, Stuttgart)-> (7,1) and (1,7)
# -----------------------------------------------------------------------------
allowed_flights = {
    (2,4), (4,2),
    (6,4), (4,6),
    (1,4), (4,1),
    (1,0), (0,1),
    (0,4), (4,0),
    (5,4), (4,5),
    (4,3), (3,4),
    (7,4), (4,7),
    (0,2), (2,0),
    (5,0), (0,5),
    (7,5), (5,7),
    (6,7),  # one-way: from Reykjavik to Stuttgart
    (5,2), (2,5),
    (1,5), (5,1),
    (1,2), (2,1),
    (7,1), (1,7)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation (ordering) of the 8 cities:
#   pos[i] : the city (index) visited at itinerary position i, 0 <= i < 8.
#   S[i]   : the arrival day at the city visited at position i.
#
# For the first city (i==0): the visit interval is [S[i], S[i] + duration - 1].
# For every subsequent city (i>=1): the effective visit interval is [S[i], S[i] + duration - 2]
#   (one day is lost due to the flight).
#
# The departure day from the final city must equal total_trip, 23.
# -----------------------------------------------------------------------------
n = 8
total_trip = 23
s = Solver()

# Itinerary as a permutation of the 8 cities.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector.
S = IntVector("S", n)
s.add(S[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions for durations at itinerary positions.
def full_duration(i):
    # For the first city, full duration is used.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

def effective_duration(i):
    # For cities i>=1, effective duration = duration - 1.
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
# For the final city (position n-1):
#   If it's not the first city, the departure day is S[n-1] + (duration - 1) - 1 = S[n-1] + duration - 2.
# This final departure day must equal total_trip (23).
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair in the itinerary, there must be a direct flight.
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
# For each city with an event, if that city is visited at itinerary position i then
# its visit interval must cover the event window.
#
# The visit interval for a city visited at position i is:
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
    arrivals = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city_index = itinerary[i]
        city_name = cities[city_index]
        if i == 0:
            departure = arrivals[i] + durations[city_index] - 1
        else:
            departure = arrivals[i] + durations[city_index] - 2
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    
    # Compute final trip end
    last_city = itinerary[n-1]
    if n-1 == 0:
        final_departure = arrivals[n-1] + durations[last_city] - 1
    else:
        final_departure = arrivals[n-1] + durations[last_city] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")