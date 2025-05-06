from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 7 cities:
# 0: Valencia – 5 days.
# 1: Riga     – 5 days.
# 2: Prague   – 3 days.
#              Event: Visit relatives in Prague between day 7 and day 9.
# 3: Mykonos  – 3 days.
#              Event: Attend a wedding in Mykonos between day 1 and day 3.
# 4: Zurich   – 5 days.
# 5: Bucharest– 5 days.
# 6: Nice     – 2 days.
#
# Total planned days = 5 + 5 + 3 + 3 + 5 + 5 + 2 = 28.
# There are 6 flight transitions (7 cities), so the effective trip duration
# becomes 28 - 6 = 22 days.
#
# Note:
# - For the first visited city, you have its full planned duration.
# - For each subsequent city, one day is "lost" to flying. That is, the effective
#   visit interval is: [arrival, arrival + duration - 2].
# -----------------------------------------------------------------------------
cities    = ["Valencia", "Riga", "Prague", "Mykonos", "Zurich", "Bucharest", "Nice"]
durations = [5,          5,      3,       3,         5,        5,         2]

# Event windows: for cities with an event, we require that the visit interval
# covers from the event's lower bound to its upper bound.
# For Prague (index 2): relatives between day 7 and day 9.
# For Mykonos (index 3): wedding between day 1 and day 3.
events = {
    2: (7, 9),
    3: (1, 3)
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# Provided flights (bidirectional):
# - Mykonos and Nice         -> (3,6) and (6,3)
# - Mykonos and Zurich       -> (3,4) and (4,3)
# - Prague and Bucharest     -> (2,5) and (5,2)
# - Valencia and Bucharest   -> (0,5) and (5,0)
# - Zurich and Prague        -> (4,2) and (2,4)
# - Riga and Nice            -> (1,6) and (6,1)
# - Zurich and Riga          -> (4,1) and (1,4)
# - Zurich and Bucharest     -> (4,5) and (5,4)
# - Zurich and Valencia      -> (4,0) and (0,4)
# - Bucharest and Riga       -> (5,1) and (1,5)
# - Prague and Riga          -> (2,1) and (1,2)
# - Prague and Valencia      -> (2,0) and (0,2)
# - Zurich and Nice          -> (4,6) and (6,4)
# -----------------------------------------------------------------------------
allowed_flights = {
    (3, 6), (6, 3),
    (3, 4), (4, 3),
    (2, 5), (5, 2),
    (0, 5), (5, 0),
    (4, 2), (2, 4),
    (1, 6), (6, 1),
    (4, 1), (1, 4),
    (4, 5), (5, 4),
    (4, 0), (0, 4),
    (5, 1), (1, 5),
    (2, 1), (1, 2),
    (2, 0), (0, 2),
    (4, 6), (6, 4)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation of the 7 cities:
#    pos[i] : City index visited at itinerary position i, for i in 0..6.
#    S[i]   : Arrival day at the city in position i.
#
# For the first city (i == 0):
#    Visit interval is [S[0], S[0] + durations[city] - 1].
# For every subsequent city (i >= 1):
#    Visit interval is [S[i], S[i] + durations[city] - 2].
#
# The departure day of the final city must equal total_trip = 22.
# -----------------------------------------------------------------------------
n = 7
total_trip = 22
s = Solver()

# Ensure permutation: each city appears exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days for each city.
S = IntVector("S", n)
s.add(S[0] == 1)   # The trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions: 
# full_duration(i): duration of visit at itinerary position i if it is the first city.
# effective_duration(i): for subsequent cities, effective duration = planned duration - 1.
def full_duration(i):
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

def effective_duration(i):
    # For subsequent cities: effective duration = duration - 1.
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1: S[1] = S[0] + (full_duration of city at pos[0]).
# For positions 2 to n-1: S[i] = S[i-1] + (effective_duration of city at pos[i-1]).
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# The departure day from the final city is computed as:
#   If v is the city at position n-1 then
#       if n-1 == 0: departure = S[n-1] + durations[v] - 1,
#       otherwise: departure = S[n-1] + durations[v] - 1  (since effective_duration equals duration - 1)
#
# We impose that the final departure equals total_trip:
#   S[n-1] + effective_duration(n-1) - 1 == total_trip
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Direct flight connectivity:
#
# For every consecutive pair of cities in the itinerary, there must be a direct flight.
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
# For each event city, if that city is visited at itinerary position i, then
# its visit interval must cover the event window.
#
# The visit interval is defined as:
# - if i == 0 (first city): [S[i], S[i] + durations[city] - 1]
# - if i >= 1: [S[i], S[i] + durations[city] - 2]
#
# For Prague (city index 2): require S[i] <= 7 and departure >= 9.
# For Mykonos (city index 3): require S[i] <= 1 and departure >= 3.
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
        city = cities[itinerary[i]]
        if i == 0:
            departure = arrivals[i] + durations[itinerary[i]] - 1
        else:
            departure = arrivals[i] + durations[itinerary[i]] - 2
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    
    last_city = itinerary[-1]
    if n - 1 == 0:
        final_departure = arrivals[-1] + durations[last_city] - 1
    else:
        final_departure = arrivals[-1] + durations[last_city] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")