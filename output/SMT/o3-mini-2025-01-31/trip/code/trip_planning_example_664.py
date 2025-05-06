from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 6 cities:
# 0: Tallinn   – 2 days.
# 1: Bucharest – 4 days.
#              Event: Visit relatives in Bucharest between day 1 and day 4.
# 2: Seville   – 5 days.
#              Event: Meet friends in Seville between day 8 and day 12.
# 3: Stockholm – 5 days.
# 4: Munich    – 5 days.
#              Event: Wedding in Munich between day 4 and day 8.
# 5: Milan     – 2 days.
#
# Total planned days = 2 + 4 + 5 + 5 + 5 + 2 = 23.
# There are 5 flight transitions, so effective trip duration = 23 - 5 = 18 days.
#
# Notes:
# - The trip starts on day 1.
# - In the first city you use its full planned duration.
# - In every subsequent city, one day is "lost" due to the flight.
# -----------------------------------------------------------------------------

cities    = ["Tallinn", "Bucharest", "Seville", "Stockholm", "Munich", "Milan"]
durations = [2,         4,         5,        5,         5,      2]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    1: (1, 4),    # Bucharest: visit relatives between day 1 and 4.
    2: (8, 12),   # Seville: meet friends between day 8 and 12.
    4: (4, 8)     # Munich: wedding between day 4 and 8.
}

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# Flights (bidirectional unless noted otherwise):
#
# - Milan and Stockholm   -> (5,3) and (3,5)
# - Munich and Stockholm  -> (4,3) and (3,4)
# - Bucharest and Munich    -> (1,4) and (4,1)
# - Munich and Seville      -> (4,2) and (2,4)
# - Stockholm and Tallinn   -> (3,0) and (0,3)
# - Munich and Milan        -> (4,5) and (5,4)
# - Munich and Tallinn      -> (4,0) and (0,4)
# - Seville and Milan       -> (2,5) and (5,2)
# -----------------------------------------------------------------------------

allowed_flights = {
    (5,3), (3,5),
    (4,3), (3,4),
    (1,4), (4,1),
    (4,2), (2,4),
    (3,0), (0,3),
    (4,5), (5,4),
    (4,0), (0,4),
    (2,5), (5,2)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We model an itinerary as an ordering (permutation) of the 6 cities:
#   pos[i] : index of the city visited at itinerary position i, for i = 0,...,5.
#   S[i]   : arrival day at the city visited at position i.
#
# For each city at itinerary position i:
#   - If i == 0 (first city): effective stay = full planned duration.
#       Departure day = S[0] + durations[city] - 1.
#   - If i >= 1: effective stay = planned duration - 1.
#       Departure day = S[i] + (durations[city] - 1) - 1.
#
# The departure day of the final city must equal day 18.
# -----------------------------------------------------------------------------

n = 6
s = Solver()

# Itinerary positions (permutation of cities)
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1: S[1] = S[0] + (full planned duration of city at pos[0]).
# For positions i >= 2: 
#   S[i] = S[i-1] + (duration of city at pos[i-1] - 1).
# -----------------------------------------------------------------------------

# Position 1:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    /* pos[0]==4 */ durations[4] if pos[0]==4 else durations[5]))))
    # Note: we can also use an If for pos[0]==5
)
# To ensure correctness for both possibilities when pos[0]==4 or pos[0]==5:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    If(pos[0] == 4, durations[4],
       durations[5]))))
)

# Positions 2 to n-1:
for i in range(2, n):
    s.add(
        S_days[i] ==
        S_days[i-1] +
        If(pos[i-1] == 0, durations[0] - 1,
        If(pos[i-1] == 1, durations[1] - 1,
        If(pos[i-1] == 2, durations[2] - 1,
        If(pos[i-1] == 3, durations[3] - 1,
        If(pos[i-1] == 4, durations[4] - 1,
           durations[5] - 1)))))
    )

# Trip end constraint:
# For the last city (i = n-1) the effective stay = (duration - 1),
# so departure day = S_days[n-1] + (durations - 1) - 1 must equal 18.
last_effective = If(pos[n-1] == 0, durations[0] - 1,
                If(pos[n-1] == 1, durations[1] - 1,
                If(pos[n-1] == 2, durations[2] - 1,
                If(pos[n-1] == 3, durations[3] - 1,
                If(pos[n-1] == 4, durations[4] - 1,
                durations[5] - 1)))))
s.add(S_days[n-1] + last_effective - 1 == 18)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For every consecutive pair in the itinerary, there must be a direct flight.
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
# For cities with events, if the city appears at itinerary position i,
# then its visitation interval must overlap with the event window.
#
# For the first city (i == 0), interval = [S, S + durations[city] - 1].
# For subsequent cities (i >= 1), interval = [S, S + (durations[city] - 1) - 1],
# i.e., [S, S + durations[city] - 2].
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
        city_index = itinerary[i]
        city_name = cities[city_index]
        # Calculate effective stay:
        if i == 0:
            effective = durations[city_index]
        else:
            effective = durations[city_index] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")