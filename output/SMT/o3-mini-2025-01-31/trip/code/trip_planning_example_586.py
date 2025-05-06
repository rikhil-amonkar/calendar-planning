from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 5 cities:
# 0: Frankfurt – 3 days.
# 1: Naples   – 4 days.
# 2: Helsinki – 4 days.
#              Event: Annual show in Helsinki from day 2 to day 5.
# 3: Lyon     – 3 days.
# 4: Prague   – 2 days.
#              Event: Workshop in Prague between day 1 and day 2.
#
# Total planned days = 3 + 4 + 4 + 3 + 2 = 16.
# There are 4 flight transitions, so effective trip duration = 16 - 4 = 12 days.
#
# Note:
# - The trip starts on day 1 and you have the full planned duration in the first city.
# - In every subsequent city one day is "lost" via flights, so effective stay = duration - 1.
# -----------------------------------------------------------------------------
cities    = ["Frankfurt", "Naples", "Helsinki", "Lyon", "Prague"]
durations = [3,           4,       4,         3,     2]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    2: (2, 5),   # In Helsinki, the annual show must be attended between day 2 and day 5.
    4: (1, 2)    # In Prague, the workshop must be attended between day 1 and day 2.
}

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional):
#
# 1. Prague and Lyon      -> (Prague, Lyon) and (Lyon, Prague)   -> (4,3) and (3,4)
# 2. Prague and Frankfurt -> (Prague, Frankfurt) and (Frankfurt, Prague) -> (4,0) and (0,4)
# 3. Frankfurt and Lyon   -> (Frankfurt, Lyon) and (Lyon, Frankfurt) -> (0,3) and (3,0)
# 4. Helsinki and Naples  -> (Helsinki, Naples) and (Naples, Helsinki) -> (2,1) and (1,2)
# 5. Helsinki and Frankfurt-> (Helsinki, Frankfurt) and (Frankfurt, Helsinki) -> (2,0) and (0,2)
# 6. Naples and Frankfurt  -> (Naples, Frankfurt) and (Frankfurt, Naples) -> (1,0) and (0,1)
# 7. Prague and Helsinki  -> (Prague, Helsinki) and (Helsinki, Prague) -> (4,2) and (2,4)
# -----------------------------------------------------------------------------
allowed_flights = {
    (4,3), (3,4),
    (4,0), (0,4),
    (0,3), (3,0),
    (2,1), (1,2),
    (2,0), (0,2),
    (1,0), (0,1),
    (4,2), (2,4)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as an ordering (permutation) of the 5 cities:
#  pos[i]: the city visited at itinerary position i (i=0,...,4).
#  S[i]: the arrival day at that city.
#
# For the first city (i==0): the visit interval is [S, S + duration - 1].
# For each subsequent city (i>=1): the effective visit interval is [S, S + duration - 2]
#    (one day is lost because of the flight).
#
# The departure day from the final city must equal 12.
# -----------------------------------------------------------------------------
n = 5
total_trip = 12
s = Solver()

# Itinerary: permutation of 5 cities.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days: S[0..n-1]
S = IntVector("S", n)
s.add(S[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For the first transition:
#   S[1] = S[0] + (full duration of city visited at pos[0])
# For i>=2:
#   S[i] = S[i-1] + (duration at pos[i-1] - 1)
# -----------------------------------------------------------------------------
# For position 1:
s.add(
    S[1] == S[0] +
      If(pos[0] == 0, durations[0],
      If(pos[0] == 1, durations[1],
      If(pos[0] == 2, durations[2],
      If(pos[0] == 3, durations[3],
         durations[4]))))
)

# For positions 2 to 4:
for i in range(2, n):
    s.add(
        S[i] == S[i-1] +
          If(pos[i-1] == 0, durations[0] - 1,
          If(pos[i-1] == 1, durations[1] - 1,
          If(pos[i-1] == 2, durations[2] - 1,
          If(pos[i-1] == 3, durations[3] - 1,
             durations[4] - 1))))
    )

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the final city (position n-1):
#   If pos[n-1] is not the first city then effective departure = S[n-1] + (duration - 1) - 1
#                                                       = S[n-1] + duration - 2.
# This final departure must equal total_trip (12).
# -----------------------------------------------------------------------------
s.add(
    S[n-1] +
    If(pos[n-1] == 0, durations[0] - 1,
    If(pos[n-1] == 1, durations[1] - 1,
    If(pos[n-1] == 2, durations[2] - 1,
    If(pos[n-1] == 3, durations[3] - 1,
         durations[4] - 1)))) - 1
    == total_trip
)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair (i, i+1) in the itinerary, there must be a direct flight.
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
# For each event city visited at position i, its visit interval must cover the event window.
#
# The visit interval:
#  - For i == 0 (first city): [S, S + duration - 1]
#  - For i >= 1: [S, S + (duration - 1) - 1] = [S, S + duration - 2]
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
        city_idx = itinerary[i]
        city_name = cities[city_idx]
        if i == 0:
            departure = arrivals[i] + durations[city_idx] - 1
        else:
            departure = arrivals[i] + durations[city_idx] - 2
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    # Compute final trip end
    final_city = itinerary[n-1]
    if n-1 == 0:
        final_departure = arrivals[n-1] + durations[final_city] - 1
    else:
        final_departure = arrivals[n-1] + durations[final_city] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")