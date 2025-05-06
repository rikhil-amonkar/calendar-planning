from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 3 cities:
# 0: Mykonos  – 6 days.
#    Event: You must attend a conference in Mykonos on both day 4 and day 9.
#           (We require that the visit interval covers day 4 and day 9.)
# 1: Budapest – 3 days.
# 2: Hamburg  – 2 days.
#
# Total planned days = 6 + 3 + 2 = 11.
# There are 2 flights between cities, so the effective trip duration = 11 - 2 = 9 days.
#
# Note:
# - In the first visited city the full planned duration is used (interval = [S, S + duration - 1]).
# - In every subsequent city one day is lost to flying (interval = [S, S + duration - 2]).
# -----------------------------------------------------------------------------
cities    = ["Mykonos", "Budapest", "Hamburg"]
durations = [6,         3,         2]

# Event requirement for Mykonos:
# We require that if Mykonos is visited at itinerary position i then:
#   its visit interval must cover day 4 and day 9.
# That is, if city = Mykonos then:
#   For first city: S[i] <= 4    and  S[i] + (6 - 1) >= 9.
#   For later cities: S[i] <= 4    and  S[i] + (6 - 2) >= 9.
events = {
    0: (4, 9)  # meaning arrival must be no later than day 4 and departure no earlier than day 9.
}

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# Given flights:
# - Budapest and Mykonos -> bidirectional: (Mykonos,Budapest) and (Budapest,Mykonos)
# - Hamburg and Budapest  -> bidirectional: (Budapest,Hamburg) and (Hamburg,Budapest)
#
# There is no direct flight between Mykonos and Hamburg.
# -----------------------------------------------------------------------------
allowed_flights = {
    (0, 1), (1, 0),  # Mykonos <--> Budapest
    (1, 2), (2, 1)   # Budapest <--> Hamburg
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation of the 3 cities.
#   pos[i] : the city index visited at itinerary position i (for i in 0,1,2).
#   S[i]   : the arrival day at the city visited at position i.
#
# For the first city (i == 0): visit interval is [S[0], S[0] + durations[city] - 1].
# For each subsequent city (i >= 1): visit interval is [S[i], S[i] + durations[city] - 2].
#
# The departure day from the final city must equal total_trip = 9.
# -----------------------------------------------------------------------------
n = 3
total_trip = 9
s = Solver()

# Permutation: each city appears exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival day for each visited city.
# (Typically we fix the trip’s start day S[0] to 1.)
S = IntVector("S", n)
s.add(S[0] == 1)
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions: full duration for the first city and effective duration for subsequents.
def full_duration(i):
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])
def effective_duration(i):
    # For subsequent cities: effective duration = planned duration - 1.
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1: S[1] = S[0] + (full_duration of city at pos[0]).
# For positions >= 2: S[i] = S[i-1] + (effective_duration of city at pos[i-1]).
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# The departure day from the final city equals:
#   If first city: S[n-1] + durations[city] - 1.
#   Otherwise: S[n-1] + (durations[city] - 1) [since effective_duration = duration - 1].
#
# Our constraint is:
#   S[n-1] + effective_duration(n-1) - 1 == total_trip.
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair of cities (i and i+1),
# there must be a direct flight between the cities.
# -----------------------------------------------------------------------------
for i in range(n - 1):
    flight_opts = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                flight_opts.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(flight_opts))

# -----------------------------------------------------------------------------
# Event constraints:
#
# For each city with a conference event, if that city is visited at itinerary
# position i then its visit interval must cover both required days.
#
# For Mykonos:
#   if i == 0 (first city): require S[i] <= 4 and S[i] + (6 - 1) >= 9.
#   if i >= 1 (later city): require S[i] <= 4 and S[i] + (6 - 2) >= 9.
# -----------------------------------------------------------------------------
for i in range(n):
    # For city index 0 (Mykonos)
    s.add(
        If(pos[i] == 0,
           And(
               S[i] <= events[0][0],
               If(i == 0,
                  S[i] + durations[0] - 1 >= events[0][1],
                  S[i] + durations[0] - 2 >= events[0][1]
               )
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
        print(f" Position {i+1}: {city:8s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    # Final trip end day
    last_city = itinerary[-1]
    if n - 1 == 0:
        final_departure = arrivals[-1] + durations[last_city] - 1
    else:
        final_departure = arrivals[-1] + durations[last_city] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")