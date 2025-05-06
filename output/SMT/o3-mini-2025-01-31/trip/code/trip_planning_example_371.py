from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 4 cities:
# 0: Nice      – 2 days.
# 1: Stockholm – 5 days.
# 2: Split     – 3 days.
#               Event: Conference in Split between day 7 and day 9.
# 3: Vienna    – 2 days.
#               Event: Workshop in Vienna between day 1 and day 2.
#
# Total planned days = 2 + 5 + 3 + 2 = 12.
# There are 3 flight transitions, so the effective trip duration = 12 - 3 = 9 days.
#
# Note:
#  - The trip starts on day 1 in the first city and you get its full duration.
#  - In each subsequent city, 1 day is “lost” due to the flight (so effective duration = duration - 1).
# -----------------------------------------------------------------------------
cities    = ["Nice", "Stockholm", "Split", "Vienna"]
durations = [2,       5,         3,       2]

# Events: mapping city index -> (event_start, event_end)
events = {
    2: (7, 9),   # In Split, conference must be attended between day 7 and 9.
    3: (1, 2)    # In Vienna, workshop must be attended between day 1 and 2.
}

# -----------------------------------------------------------------------------
# Allowed direct flights between cities (bidirectional unless stated otherwise):
#
# 1. Vienna and Stockholm      -> (Vienna, Stockholm) and (Stockholm, Vienna)
# 2. Vienna and Nice            -> (Vienna, Nice) and (Nice, Vienna)
# 3. Vienna and Split           -> (Vienna, Split) and (Split, Vienna)
# 4. Stockholm and Split        -> (Stockholm, Split) and (Split, Stockholm)
# 5. Nice and Stockholm         -> (Nice, Stockholm) and (Stockholm, Nice)
# -----------------------------------------------------------------------------
allowed_flights = {
    (3, 1), (1, 3),     # Vienna <-> Stockholm
    (3, 0), (0, 3),     # Vienna <-> Nice
    (3, 2), (2, 3),     # Vienna <-> Split
    (1, 2), (2, 1),     # Stockholm <-> Split
    (0, 1), (1, 0)      # Nice <-> Stockholm
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as a permutation of the 4 cities.
# pos[i] : the index of the city visited at itinerary position i (i=0,...,3).
# S[i]   : arrival day at the city visited at position i.
#
# For the first city (i==0): you use its full duration.
# For each subsequent city (i>=1): effective stay = (duration - 1) days.
#
# The departure day from the final city must equal 9.
# -----------------------------------------------------------------------------
n = 4
total_trip = 9
s = Solver()

# Permutation of cities.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days.
S = IntVector("S", n)
s.add(S[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For the first transition:
#   Departure from pos[0] = S[0] + (full duration - 1)
#   S[1] = departure + 1 = S[0] + full_duration[pos[0]]
#
# For subsequent transitions (i >= 2):
#   Departure from pos[i-1] = S[i-1] + (duration - 1) - 1 = S[i-1] + duration - 2
#   S[i] = S[i-1] + (duration[pos[i-1]] - 1)
# -----------------------------------------------------------------------------
# For position 1:
s.add(
    S[1] ==
    S[0] + 
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
       durations[3])))
)

# For positions 2 and 3:
for i in range(2, n):
    s.add(
        S[i] ==
        S[i-1] +
        If(pos[i-1] == 0, durations[0] - 1,
        If(pos[i-1] == 1, durations[1] - 1,
        If(pos[i-1] == 2, durations[2] - 1,
           durations[3] - 1)))
    )

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the final city at position n-1:
#   If it is not the first city, effective stay = duration - 1 so
#   Departure = S[n-1] + (duration - 1) - 1 = S[n-1] + duration - 2.
# This departure must equal total_trip (9).
# -----------------------------------------------------------------------------
s.add(
    S[n-1] + 
    If(pos[n-1] == 0, durations[0] - 1,
    If(pos[n-1] == 1, durations[1] - 1,
    If(pos[n-1] == 2, durations[2] - 1,
       durations[3] - 1))) - 1
    == total_trip
)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair of visits (i and i+1),
# there must be a direct flight from pos[i] to pos[i+1].
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
# For cities with events, if city is visited at itinerary position i,
# then its visit interval [arrival, departure] must cover the event window.
#
# For position i==0 (first city):
#   Departure = S[i] + durations[city] - 1.
# For i>=1:
#   Departure = S[i] + (durations[city] - 1) - 1 = S[i] + durations[city] - 2.
#
# We require:
#   S[i] <= event_end   and   departure >= event_start.
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
            effective = durations[city_index]
            departure = arrivals[i] + durations[city_index] - 1
        else:
            effective = durations[city_index] - 1
            departure = arrivals[i] + durations[city_index] - 2
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    # Final trip end:
    final_city = itinerary[n-1]
    if n-1 == 0:
        final_departure = arrivals[n-1] + durations[final_city] - 1
    else:
        final_departure = arrivals[n-1] + durations[final_city] - 2
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")