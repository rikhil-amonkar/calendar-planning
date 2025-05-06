from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 3 cities:
# 0: Krakow    – 2 days.
#              Event: Attend a wedding in Krakow between day 9 and day 10.
# 1: Dubrovnik – 7 days.
# 2: Frankfurt  – 3 days.
#
# Planned total days = 2 + 7 + 3 = 12 days.
# There are 2 flights (since we visit 3 cities),
# so the effective trip duration = 12 - 2 = 10 days.
#
# Note on timing:
#   In the first visited city the full planned duration is used:
#     Visit interval = [arrival, arrival + duration - 1]
#   For each subsequent city one day is “lost” to the flight, so the 
#     effective visit interval = [arrival, arrival + (duration - 1) - 1]
#     (i.e. [arrival, arrival + duration - 2])
#
# For the wedding event in Krakow (a 2‐day stay) the interval must cover
# day 9 and day 10. That forces the visit interval for Krakow to be exactly [9, 10].
# Hence, if Krakow is visited as the first city then its arrival must be 9,
# and if it is visited later then its arrival (S) must also equal 9.
#
# With our “rigid” time model (i.e. no waiting time beyond the planned duration)
# the arrival times are completely determined by the order of visits.
# -----------------------------------------------------------------------------
cities    = ["Krakow", "Dubrovnik", "Frankfurt"]
durations = [2,         7,           3]

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# Given flights:
#  - "Frankfurt and Krakow" gives flights in both directions between Frankfurt (2)
#    and Krakow (0).
#  - "Dubrovnik and Frankfurt" gives flights in both directions between Dubrovnik (1)
#    and Frankfurt (2).
#
# There is no direct flight between Krakow and Dubrovnik.
# -----------------------------------------------------------------------------
allowed_flights = {
    (0, 2), (2, 0),   # Krakow <-> Frankfurt
    (1, 2), (2, 1)    # Dubrovnik <-> Frankfurt
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation of the 3 cities:
#   pos[i] : the city index visited at itinerary position i, for i in {0,1,2}.
#   S[i]   : the arrival day at the city visited at position i.
#
# We impose that the trip “starts” on day 1:
#   S[0] == 1.
#
# Also, the departure from a city is determined by its visit interval:
#   For the first city: interval = [S[i], S[i] + duration - 1].
#   For a subsequent city: interval = [S[i], S[i] + duration - 2].
#
# The trip finish constraint is that the departure (end) day of the final city
# equals 10.
#
# With the (fixed) planned durations and the fact that there are 2 flights,
# it must hold that:
#    (2 + 7 + 3) - 2 = 10.
# -----------------------------------------------------------------------------
n = 3
total_trip = 10
s = Solver()

# Permutation: each city appears exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days for each visited city.
# We fix the start day to 1.
S = IntVector("S", n)
s.add(S[0] == 1)
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions to pick the planned duration (or effective duration) based on the city 
def full_duration(i):
    # For the first city in the itinerary, we use the full planned duration.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])
    
def effective_duration(i):
    # For subsequent cities, one day is lost due to the flight.
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# The arrival time for city at position 1 is:
#   S[1] = S[0] + full_duration(0)
#
# For any city at position i (i >= 2):
#   S[i] = S[i-1] + effective_duration(i-1)
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))
    
# -----------------------------------------------------------------------------
# Final trip end constraint:
#
# For the final city at position n-1 (which is not the first city),
# its departure day is given by:
#   departure = S[n-1] + effective_duration(n-1) - 1
#
# We require:
#   S[n-1] + effective_duration(n-1) - 1 == total_trip
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Direct flight connectivity constraints:
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
# Wedding event constraint for Krakow:
#
# The wedding in Krakow must be attended between day 9 and day 10.
# Because the stay in Krakow is 2 days long, its visit interval is:
#   - if it is the first city: [S, S+1]
#   - if it is not the first city: [S, S+ (2-1)] = [S, S+1]
#
# To cover the wedding window [9, 10], it is necessary that S (the arrival day)
# equals 9.
#
# We add: if a city in the itinerary is Krakow (city 0) then its arrival S must equal 9.
# -----------------------------------------------------------------------------
for i in range(n):
    s.add(If(pos[i] == 0, S[i] == 9, True))

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