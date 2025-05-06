from z3 import Solver, Int, IntVector, Distinct, Sum, And, Or, If, sat

# -----------------------------------------------------------------------------
# Problem Data:
# We have 6 cities with the following planned durations and event constraints:
#
#   City         Duration   Event Constraint (visit window condition)
#   ---------------------------------------------------------------
#   Helsinki       2       Workshop between day 1 and day 2.
#   Warsaw         3       Visit relatives between day 9 and day 11.
#   Madrid         4       No specific event.
#   Split          4       No specific event.
#   Reykjavik      2       Meet a friend between day 8 and day 9.
#   Budapest       4       No specific event.
#
# Total planned visit durations = 2+3+4+4+2+4 = 19.
# When visiting n cities, the trip length is computed as:
#    First city: full duration
#    Each subsequent city: duration - 1 (since the flight “loses” one day)
# So total effective trip days = 19 - (6-1) = 19 - 5 = 14.
#
# We thus want our schedule to exactly span 14 days.
#
# ----------------------------------------------------------------------------- 
# Allowed direct flights (each pair is bidirectional unless noted otherwise):
#
#  Helsinki <-> Reykjavik       (0,4) and (4,0)
#  Budapest <-> Warsaw           (5,1) and (1,5)
#  Madrid <-> Split              (2,3) and (3,2)
#  Helsinki <-> Split            (0,3) and (3,0)
#  Helsinki <-> Madrid           (0,2) and (2,0)
#  Helsinki <-> Budapest         (0,5) and (5,0)
#  Reykjavik <-> Warsaw          (4,1) and (1,4)
#  Helsinki <-> Warsaw           (0,1) and (1,0)
#  Madrid <-> Budapest           (2,5) and (5,2)
#  Budapest <-> Reykjavik        (5,4) and (4,5)
#  Madrid <-> Warsaw             (2,1) and (1,2)
#  Warsaw <-> Split              (1,3) and (3,1)
#  From Reykjavik to Madrid      (4,2) only (directed flight)
#
# For indexing, we assign:
#   0: Helsinki
#   1: Warsaw
#   2: Madrid
#   3: Split
#   4: Reykjavik
#   5: Budapest
#
# -----------------------------------------------------------------------------
# Set up the Z3 model.

cities   = ["Helsinki", "Warsaw", "Madrid", "Split", "Reykjavik", "Budapest"]
durations = [2, 3, 4, 4, 2, 4]  # durations as given
n = len(cities)
total_trip = 14

solver = Solver()

# Decision variables:
# pos[i] represents the city index visited in position i.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] : arrival day at the city in itinerary position i.
S = IntVector("S", n)
# The trip begins at day 1.
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Introduce waiting days between visits for transitions.
# There are n-1 transitions. In general, extra waiting days would allow flexibility.
# In our case, the effective trip length is: S[0] + duration(first) + sum_{i=1}^{n-1} (duration - 1) + waiting
# We need the trip to be exactly total_trip days, and
# since sum(durations) - (n-1) = 14, waiting days sum must be 0.
w = IntVector("w", n-1)
for i in range(n-1):
    solver.add(w[i] >= 0)
solver.add(Sum(w) == 0)

# Recurrence for arrival days:
# For position 1: S[1] = S[0] + (full duration of first city) + waiting[0]
# For position i>=2: S[i] = S[i-1] + (duration(previous) - 1) + waiting[i-1]
for i in range(1, n):
    if i == 1:
        solver.add(
            S[i] == S[0] + 
            Sum([If(pos[0] == c, durations[c], 0) for c in range(n)]) + w[0]
        )
    else:
        solver.add(
            S[i] == S[i-1] + 
            Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]) + w[i-1]
        )

# Final departure day constraint:
# Trip ends at: arrival S[n-1] + (duration(last) - 1) should equal total_trip.
solver.add(
    S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip
)

# Allowed direct flights:
# List all allowed flight pairs (a, b) meaning a direct flight exists from 'a' to 'b'.
allowed_flights = {
    (0,4), (4,0),                  # Helsinki <-> Reykjavik
    (5,1), (1,5),                  # Budapest <-> Warsaw
    (2,3), (3,2),                  # Madrid <-> Split
    (0,3), (3,0),                  # Helsinki <-> Split
    (0,2), (2,0),                  # Helsinki <-> Madrid
    (0,5), (5,0),                  # Helsinki <-> Budapest
    (4,1), (1,4),                  # Reykjavik <-> Warsaw
    (0,1), (1,0),                  # Helsinki <-> Warsaw
    (2,5), (5,2),                  # Madrid <-> Budapest
    (5,4), (4,5),                  # Budapest <-> Reykjavik
    (2,1), (1,2),                  # Madrid <-> Warsaw
    (1,3), (3,1),                  # Warsaw <-> Split
    (4,2)                         # directed from Reykjavik to Madrid
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

for i in range(n-1):
    flight_options = []
    for a in range(n):
        for b in range(n):
            if flight_allowed(a, b):
                flight_options.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(flight_options))

# Event Constraints:
# For every position i, if the city has an event, constrain the arrival day S[i]
for i in range(n):
    # Create boolean predicates for each city based on its index.
    isHelsinki  = (pos[i] == 0)
    isWarsaw    = (pos[i] == 1)
    isMadrid    = (pos[i] == 2)
    isSplit     = (pos[i] == 3)
    isReykjavik = (pos[i] == 4)
    isBudapest  = (pos[i] == 5)
    
    # For Helsinki: workshop between day 1 and day 2.
    # Its visit interval is [S, S+ (2-1)] = [S, S+1]. For the interval to cover at least one day in [1,2]:
    # we require S <= 2 and S+1 >= 1. (S+1 >= 1 is always true since S>=1)
    solver.add(If(isHelsinki, S[i] <= 2, True))
    
    # For Warsaw: relatives between day 9 and day 11.
    # Visit interval: [S, S+2]. Need S <= 11 and S+2 >= 9  => S >= 7.
    solver.add(If(isWarsaw, And(S[i] >= 7, S[i] <= 11), True))
    
    # For Reykjavik: meet a friend between day 8 and day 9.
    # Visit interval: [S, S+1]. Need S <= 9 and S+1 >= 8  => S >= 7.
    solver.add(If(isReykjavik, And(S[i] >= 7, S[i] <= 9), True))
    
    # Additional: Cities with event windows that are incompatible with S[0] = 1 must not be first.
    if i == 0:
        # Warsaw and Reykjavik have events that require S >= 7; therefore, they cannot be visited first.
        solver.add(And(pos[0] != 1, pos[0] != 4))

# -----------------------------------------------------------------------------
# Solve the model.
# -----------------------------------------------------------------------------
if solver.check() == sat:
    m = solver.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals  = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city_idx = itinerary[i]
        city_name = cities[city_idx]
        # Compute departure day: arrival + (duration - 1)
        departure = arrivals[i] + durations[city_idx] - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")