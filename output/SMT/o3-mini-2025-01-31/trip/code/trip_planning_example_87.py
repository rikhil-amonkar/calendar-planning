from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 3 cities:
# 0: Riga      – 2 days.
#               Event: Visit relatives in Riga between day 1 and day 2.
# 1: Amsterdam – 2 days.
# 2: Mykonos   – 5 days.
#
# Total planned duration = 2 + 2 + 5 = 9 days.
# There are 2 flight transitions, so the effective trip duration = 9 - 2 = 7 days.
#
# Note:
# - In the first city you enjoy the full duration.
# - In every subsequent city, one day is "lost" due to a flight (effective stay = duration - 1).
# -----------------------------------------------------------------------------
cities    = ["Riga", "Amsterdam", "Mykonos"]
durations = [2,       2,           5]

# Event windows: mapping city index -> (event_start, event_end)
# For Riga, we want to visit relatives between day 1 and day 2.
events = {
    0: (1, 2)
}

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# - Amsterdam and Mykonos: bidirectional -> (Amsterdam, Mykonos) and (Mykonos, Amsterdam)
# - Riga and Amsterdam: bidirectional -> (Riga, Amsterdam) and (Amsterdam, Riga)
# -----------------------------------------------------------------------------
allowed_flights = {
    (1,2), (2,1),
    (0,1), (1,0)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation (ordering) of the 3 cities:
#   pos[i] : the city index visited at itinerary position i.
#   S[i]   : the arrival day at the city visited at position i.
#
# For the first city (i == 0): visit interval = [S[i], S[i] + duration - 1].
# For every subsequent city (i >= 1): effective visit interval = [S[i], S[i] + duration - 2].
#
# The departure day from the final city must equal total_trip = 7.
# -----------------------------------------------------------------------------
n = 3
total_trip = 7
s = Solver()

# Itinerary permutation: each city appears exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(pos[i] >= 0, pos[i] < n)

# Arrival days vector.
S = IntVector("S", n)
s.add(S[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions for duration expressions at itinerary positions.
def full_duration(i):
    # For the first visited city.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])
    
def effective_duration(i):
    # For subsequent cities, effective duration = (duration - 1).
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
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
# For the final city (position n-1), the departure time is:
#   if not first city: S[n-1] + (duration - 1) - 1 = S[n-1] + duration - 2.
# This must equal total_trip (7).
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair in the itinerary (i and i+1), there must be a direct flight.
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
# For each event city visited at itinerary position i, the city's visit interval must
# cover the event window.
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
        city = itinerary[i]
        city_name = cities[city]
        if i == 0:
            departure = arrivals[i] + durations[city] - 1
        else:
            departure = arrivals[i] + durations[city] - 2
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    
    last_city = itinerary[n-1]
    if n-1 == 0:
        final_departure = arrivals[n-1] + durations[last_city] - 1
    else:
        final_departure = arrivals[n-1] + durations[last_city] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")