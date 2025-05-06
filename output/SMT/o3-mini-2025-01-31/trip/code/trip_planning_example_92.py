from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 3 cities:
# 0: Riga     – 5 days.
# 1: Vilnius  – 7 days.
# 2: Dublin   – 2 days.
#
# Planned total days = 5 + 7 + 2 = 14 days.
# There are 2 flights (since 3 cities are visited),
# so effective trip duration = 14 - 2 = 12 days.
#
# Note:
# - In the first visited city the entire planned duration is used.
#   Its visit interval is [arrival day, arrival day + duration - 1].
# - In every subsequent city one day is lost for the flight,
#   so the effective visit interval is [arrival day, arrival day + duration - 2].
# -----------------------------------------------------------------------------
cities    = ["Riga", "Vilnius", "Dublin"]
durations = [5,      7,         2]

# -----------------------------------------------------------------------------
# Allowed direct flights.
#
# Provided flights:
# - "Dublin and Riga" gives bidirectional flights between Dublin (2) and Riga (0):
#       (2,0) and (0,2)
# - "from Riga to Vilnius" is a unidirectional flight from Riga (0) to Vilnius (1)
# -----------------------------------------------------------------------------
allowed_flights = {
    (2, 0), (0, 2),
    (0, 1)  # Only from Riga to Vilnius
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation of the 3 cities:
#   pos[i] : the city index visited at itinerary position i (0 <= i < 3).
#   S[i]   : the arrival day for the city at position i.
#
# For the first city (i == 0), the visit interval is
#    [S[0], S[0] + durations[city] - 1]
# For every subsequent city (i >= 1), one day is lost to flying,
# so the visit interval is
#    [S[i], S[i] + durations[city] - 2]
#
# The final trip constraint is that the departure day from the final city is 12.
# That is:
#      S[n-1] + (durations[city] - 1) - 1 = 12,
# since for non-first cities we have an effective duration of (duration - 1).
# -----------------------------------------------------------------------------
n = 3
total_trip = 12
s = Solver()

# Permutation: each city appears exactly once.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days for each visited city. The trip starts at day 1.
S = IntVector("S", n)
s.add(S[0] == 1)
for i in range(n):
    s.add(S[i] >= 1)

# Helper functions for duration based on itinerary position:
def full_duration(i):
    # For the first city, we use its full planned duration.
    return sum([If(pos[i] == c, durations[c], 0) for c in range(n)])

def effective_duration(i):
    # For any subsequent city, effective duration = planned duration - 1.
    return sum([If(pos[i] == c, durations[c] - 1, 0) for c in range(n)])

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For the second city (i == 1): 
#   S[1] = S[0] + (full duration of the city at pos[0])
# For the third city (i == 2):
#   S[2] = S[1] + (effective duration of the city at pos[1])
# -----------------------------------------------------------------------------
s.add(S[1] == S[0] + full_duration(0))
for i in range(2, n):
    s.add(S[i] == S[i-1] + effective_duration(i-1))

# -----------------------------------------------------------------------------
# Final trip end constraint:
#
# For the final city (i == n-1, and not the first city),
# the departure day is computed as:
#   S[n-1] + (planned_duration - 1) - 1 = S[n-1] + (planned_duration - 2)
#
# We require that departure equals total_trip.
# -----------------------------------------------------------------------------
s.add(S[n-1] + effective_duration(n-1) - 1 == total_trip)

# -----------------------------------------------------------------------------
# Direct flight connectivity constraints:
#
# For every consecutive pair of cities in the itinerary, there must be a direct flight.
# -----------------------------------------------------------------------------
for i in range(n - 1):
    valid_flight = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                valid_flight.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(valid_flight))

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
        print(f" Position {i+1}: {city_name:8s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    
    # Calculate final departure day for final city
    if n-1 == 0:
        final_departure = arrivals[-1] + durations[itinerary[-1]] - 1
    else:
        final_departure = arrivals[-1] + durations[itinerary[-1]] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")