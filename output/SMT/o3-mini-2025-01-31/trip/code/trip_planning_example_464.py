from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# 0: Krakow    – 5 days.
# 1: Frankfurt – 4 days.
# 2: Oslo      – 3 days.
#      Event: Visit relatives in Oslo between day 16 and day 18.
# 3: Dubrovnik – 5 days.
#      Event: Meet friends in Dubrovnik between day 5 and day 9.
# 4: Naples    – 5 days.
#
# Total planned days = 5 + 4 + 3 + 5 + 5 = 22.
# There are 4 flight days (one per transit between consecutive cities).
# Thus, effective trip duration = 22 - 4 = 18 days.
#
# Note:
# - The trip starts on day 1.
# - For the first city, you spend the full planned duration.
# - For each later city, one day is "lost" due to the flight (effective stay = planned - 1).
# -----------------------------------------------------------------------------

cities    = ["Krakow", "Frankfurt", "Oslo", "Dubrovnik", "Naples"]
durations = [5,         4,         3,    5,          5]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    2: (16, 18),  # Oslo: visit relatives between day 16 and 18.
    3: (5, 9)     # Dubrovnik: meet friends between day 5 and 9.
}

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional):
#
# Given pairs (each allowed in both directions):
#
# Dubrovnik and Oslo     -> (3,2) and (2,3)
# Frankfurt and Krakow   -> (1,0) and (0,1)
# Frankfurt and Oslo     -> (1,2) and (2,1)
# Dubrovnik and Frankfurt-> (3,1) and (1,3)
# Krakow and Oslo        -> (0,2) and (2,0)
# Naples and Oslo        -> (4,2) and (2,4)
# Naples and Dubrovnik   -> (4,3) and (3,4)
# Naples and Frankfurt   -> (4,1) and (1,4)
# -----------------------------------------------------------------------------

allowed_flights = {
    (3,2), (2,3),
    (1,0), (0,1),
    (1,2), (2,1),
    (3,1), (1,3),
    (0,2), (2,0),
    (4,2), (2,4),
    (4,3), (3,4),
    (4,1), (1,4)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We assume the itinerary is a permutation of 5 cities.
# pos[i] represents the city index visited at position i.
# S[i] represents the arrival day at the city at position i.
#
# The constraints:
#   S[0] = 1.
#   For the first city: S[1] = S[0] + duration(city_at(pos[0])).
#   For later positions (i>=2): S[i] = S[i-1] + (duration(city_at(pos[i-1])) - 1).
#   Trip end: Departure from the last city (arrival + effective stay - 1) must equal day 18.
# -----------------------------------------------------------------------------

n = 5
s = Solver()

# The itinerary is a permutation of indices 0..4.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival times vector.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#   S[1] = S[0] + duration of city at pos[0] (full duration for first city).
# For positions 2 ... n-1:
#   S[i] = S[i-1] + (duration of city at pos[i-1] - 1).
# -----------------------------------------------------------------------------

# Constraint for the first transit (position 1).
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    /* pos[0]==4 */ durations[4])))
)

# For positions 2 to 4.
for i in range(2, n):
    s.add(
        S_days[i] ==
        S_days[i-1] +
        If(pos[i-1] == 0, durations[0] - 1,
        If(pos[i-1] == 1, durations[1] - 1,
        If(pos[i-1] == 2, durations[2] - 1,
        If(pos[i-1] == 3, durations[3] - 1,
        /* pos[i-1]==4 */ durations[4] - 1)))
    )

# Trip end constraint:
# For the last city (not the first city), the effective stay is (duration - 1).
last_effective = If(pos[n-1] == 0, durations[0] - 1,
                  If(pos[n-1] == 1, durations[1] - 1,
                  If(pos[n-1] == 2, durations[2] - 1,
                  If(pos[n-1] == 3, durations[3] - 1,
                  durations[4] - 1))))
# Departure day from last city: arrival day + effective stay - 1 must be day 18.
s.add(S_days[n-1] + last_effective - 1 == 18)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair (pos[i], pos[i+1]), ensure a direct flight exists.
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
# For cities with events, ensure that the visit interval overlaps the event window.
# The visit interval for city visited at position i is:
#   [S_days[i], S_days[i] + effective - 1],
# where effective = duration if i == 0, else (duration - 1).
#
# Event constraint: S_days[i] <= event_end and (S_days[i] + effective - 1) >= event_start.
# -----------------------------------------------------------------------------
for i in range(n):
    for city, (ev_start, ev_end) in events.items():
        s.add(
            If(pos[i] == city,
               And(
                   S_days[i] <= ev_end,
                   If(i == 0,
                      S_days[i] + durations[city] - 1 >= ev_start,
                      S_days[i] + (durations[city] - 1) - 1 >= ev_start)
               ),
               True)
        )

# -----------------------------------------------------------------------------
# Solve the scheduling problem.
# -----------------------------------------------------------------------------
if s.check() == sat:
    m = s.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals  = [m.evaluate(S_days[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city_name = cities[itinerary[i]]
        effective = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")