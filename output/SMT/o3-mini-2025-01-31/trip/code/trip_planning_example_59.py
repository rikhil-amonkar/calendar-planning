from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 3 cities:
# 0: Lyon      – 7 days.
# 1: Bucharest – 7 days.
#                Event: Attend a wedding in Bucharest between day 1 and day 7.
# 2: Porto     – 4 days.
#
# Total planned days = 7 + 7 + 4 = 18.
# There are 2 flight transitions, so effective trip duration = 18 - 2 = 16 days.
#
# Note:
# - In the first city you enjoy its full planned duration.
# - In every subsequent city, one day is "lost" due to the flight 
#   (effective stay = duration - 1).
# -----------------------------------------------------------------------------
cities    = ["Lyon", "Bucharest", "Porto"]
durations = [7,       7,         4]

# Event windows: mapping city index -> (event_start, event_end)
# For Bucharest, the wedding event must be attended between day 1 and day 7.
events = {
    1: (1, 7)
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# Provided direct flights (bidirectional):
# - Bucharest and Lyon      -> (Bucharest, Lyon) and (Lyon, Bucharest)
# - Lyon and Porto          -> (Lyon, Porto) and (Porto, Lyon)
# -----------------------------------------------------------------------------
allowed_flights = {
    (1, 0), (0, 1),
    (0, 2), (2, 0)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation (ordering) of the 3 cities:
#   pos[i] : the city index visited at itinerary position i (0 <= i < 3).
#   S[i]   : the arrival day at the city visited at position i.
#
# For the first city (i == 0): the visit interval = [S[i], S[i] + duration - 1].
# For every subsequent city (i >= 1): the effective visit interval = [S[i], S[i] + duration - 2].
#
# The departure time from the final city must equal total_trip = 16.
# -----------------------------------------------------------------------------
n = 3
total_trip = 16
s = Solver()

# Permutation variable: each city appears exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector.
S = IntVector("S", n)
s.add(S[0] == 1)  # trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions for duration expressions:
def full_duration(i):
    # For the first visited city, use full duration.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

def effective_duration(i):
    # For a visited city (not the first): effective duration = duration - 1.
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
# For the final city (position n-1):
#   If not the first city, the departure day is:
#       Departure = S[n-1] + (duration - 1) - 1 = S[n-1] + duration - 2.
# This must equal total_trip (16).
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
# For each city with an event, if that city is visited at itinerary position i,
# then its visit interval must cover the event window.
#
# - If i == 0, the interval is [S[i], S[i] + duration - 1].
# - If i >= 1, the interval is [S[i], S[i] + duration - 2].
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
    
    # Compute final trip end.
    last_city = itinerary[-1]
    if n-1 == 0:
        final_departure = arrivals[-1] + durations[last_city] - 1
    else:
        final_departure = arrivals[-1] + durations[last_city] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")