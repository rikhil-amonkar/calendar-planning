from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 7 cities:
# 0: Brussels  – 5 days.
#               Event: Workshop in Brussels between day 7 and day 11.
# 1: Rome      – 2 days.
# 2: Dubrovnik – 3 days.
# 3: Geneva    – 5 days.
# 4: Budapest  – 2 days.
#               Event: Meet friend in Budapest between day 16 and day 17.
# 5: Riga      – 4 days.
#               Event: Meet friends in Riga between day 4 and day 7.
# 6: Valencia  – 2 days.
#
# Total planned days = 5 + 2 + 3 + 5 + 2 + 4 + 2 = 23.
# There are 6 flight transitions, so the effective trip duration = 23 - 6 = 17 days.
#
# Note:
# - The trip starts on day 1 in the first city, where you enjoy its full planned duration.
# - In every subsequent city, one day is "lost" because of the flight,
#   so the effective stay = (duration - 1) days.
# -----------------------------------------------------------------------------
cities    = ["Brussels", "Rome", "Dubrovnik", "Geneva", "Budapest", "Riga", "Valencia"]
durations = [5,          2,      3,         5,       2,         4,     2]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    0: (7, 11),   # Brussels: Workshop between day 7 and day 11.
    4: (16, 17),  # Budapest: Meet friend between day 16 and day 17.
    5: (4, 7)     # Riga: Meet friends between day 4 and day 7.
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# The flights are given as pairs (a,b) where a flight exists from city a to city b.
# (All flights are bidirectional except "from Rome to Riga" which is one-way.)
#
# - Brussels and Valencia     -> (Brussels, Valencia) and (Valencia, Brussels)   -> (0,6) and (6,0)
# - Rome and Valencia         -> (Rome, Valencia) and (Valencia, Rome)               -> (1,6) and (6,1)
# - Brussels and Geneva       -> (Brussels, Geneva) and (Geneva, Brussels)           -> (0,3) and (3,0)
# - Rome and Geneva           -> (Rome, Geneva) and (Geneva, Rome)                   -> (1,3) and (3,1)
# - Dubrovnik and Geneva      -> (Dubrovnik, Geneva) and (Geneva, Dubrovnik)         -> (2,3) and (3,2)
# - Valencia and Geneva       -> (Valencia, Geneva) and (Geneva, Valencia)           -> (6,3) and (3,6)
# - from Rome to Riga         -> one-way: (Rome, Riga)                              -> (1,5)
# - Geneva and Budapest       -> (Geneva, Budapest) and (Budapest, Geneva)           -> (3,4) and (4,3)
# - Riga and Brussels         -> (Riga, Brussels) and (Brussels, Riga)               -> (5,0) and (0,5)
# - Rome and Budapest         -> (Rome, Budapest) and (Budapest, Rome)               -> (1,4) and (4,1)
# - Rome and Brussels         -> (Rome, Brussels) and (Brussels, Rome)               -> (1,0) and (0,1)
# - Brussels and Budapest     -> (Brussels, Budapest) and (Budapest, Brussels)       -> (0,4) and (4,0)
# - Dubrovnik and Rome        -> (Dubrovnik, Rome) and (Rome, Dubrovnik)             -> (2,1) and (1,2)
# -----------------------------------------------------------------------------
allowed_flights = {
    (0,6), (6,0),
    (1,6), (6,1),
    (0,3), (3,0),
    (1,3), (3,1),
    (2,3), (3,2),
    (6,3), (3,6),
    (1,5),  # one-way from Rome to Riga
    (3,4), (4,3),
    (5,0), (0,5),
    (1,4), (4,1),
    (1,0), (0,1),
    (0,4), (4,0),
    (2,1), (1,2)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation (ordering) of the 7 cities:
#   pos[i] : the city visited at itinerary position i, where 0 <= i < 7.
#   S[i]   : the arrival day at the city visited at position i.
#
# For the first city (i==0): the visit interval is [S, S + duration - 1].
# For every subsequent city (i>=1): the effective visit interval is [S, S + duration - 2]
#   (one day is lost because of the flight).
#
# The departure day from the final city must equal total_trip (17).
# -----------------------------------------------------------------------------
n = 7
total_trip = 17
s = Solver()

# Permutation: each city appears exactly once.
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
def full_duration_at(i):
    # For city at itinerary position i, full duration if first city.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

def effective_duration_at(i):
    # For subsequent positions: effective stay = duration - 1.
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#   S[1] = S[0] + (full duration of city at pos[0]).
#
# For positions i >= 2:
#   S[i] = S[i-1] + (effective duration of city at pos[i-1]).
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration_at(0))

for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration_at(i-1))

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the final city (position n-1), the departure day is:
#   if it is not the first city: S[n-1] + (duration - 1) - 1 = S[n-1] + duration - 2.
# This departure must equal total_trip (17).
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration_at(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair of itinerary positions (i and i+1), there must be a direct flight.
# -----------------------------------------------------------------------------
for i in range(n - 1):
    options = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                options.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(options))

# -----------------------------------------------------------------------------
# Event constraints:
#
# For each event city, if that city is visited at itinerary position i then its visit
# interval must cover the event window.
#
# The visit interval for a city visited at position i is:
#  - If i == 0 (first city): [S[i], S[i] + duration - 1]
#  - If i >= 1: [S[i], S[i] + duration - 2]
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
        city = itinerary[i]
        city_name = cities[city]
        # Calculate departure time
        if i == 0:
            departure = arrivals[i] + durations[city] - 1
        else:
            departure = arrivals[i] + durations[city] - 2
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    
    # Compute final trip end.
    last_city = itinerary[n-1]
    if n-1 == 0:
        final_departure = arrivals[n-1] + durations[last_city] - 1
    else:
        final_departure = arrivals[n-1] + durations[last_city] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")