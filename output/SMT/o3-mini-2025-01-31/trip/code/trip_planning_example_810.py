from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 7 cities:
# 0: Berlin     – 3 days.
#      Event: Conference in Berlin during day 1 and day 3.
# 1: Nice       – 5 days.
# 2: Athens     – 5 days.
# 3: Stockholm  – 5 days.
# 4: Barcelona  – 2 days.
#      Event: Workshop in Barcelona between day 3 and day 4.
# 5: Vilnius    – 4 days.
# 6: Lyon       – 2 days.
#      Event: Wedding in Lyon between day 4 and day 5.
#
# Total planned days = 3 + 5 + 5 + 5 + 2 + 4 + 2 = 26.
# There are 6 transitions (flights), so the effective trip duration = 26 - 6 = 20 days.
#
# Notes:
# - The trip starts on day 1.
# - In the very first city you use its full planned duration.
# - In every subsequent city one day is “lost” due to the flight (effective stay = planned duration - 1).
# -----------------------------------------------------------------------------

cities    = ["Berlin", "Nice", "Athens", "Stockholm", "Barcelona", "Vilnius", "Lyon"]
durations = [3,        5,      5,       5,          2,          4,       2]

# Events: mapping city index -> (event_start, event_end)
events = {
    0: (1, 3),  # Berlin: conference between day 1 and day 3.
    4: (3, 4),  # Barcelona: workshop between day 3 and day 4.
    6: (4, 5)   # Lyon: wedding between day 4 and day 5.
}

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# Provided pairs (bidirectional):
#
# 1. Lyon and Nice           -> (6,1) and (1,6)
# 2. Stockholm and Athens    -> (3,2) and (2,3)
# 3. Nice and Athens         -> (1,2) and (2,1)
# 4. Berlin and Athens       -> (0,2) and (2,0)
# 5. Berlin and Nice         -> (0,1) and (1,0)
# 6. Berlin and Barcelona    -> (0,4) and (4,0)
# 7. Berlin and Vilnius      -> (0,5) and (5,0)
# 8. Barcelona and Nice      -> (4,1) and (1,4)
# 9. Athens and Vilnius      -> (2,5) and (5,2)
#10. Berlin and Stockholm    -> (0,3) and (3,0)
#11. Nice and Stockholm      -> (1,3) and (3,1)
#12. Barcelona and Athens    -> (4,2) and (2,4)
#13. Barcelona and Stockholm -> (4,3) and (3,4)
#14. Barcelona and Lyon      -> (4,6) and (6,4)
# -----------------------------------------------------------------------------

allowed_flights = {
    (6,1), (1,6),
    (3,2), (2,3),
    (1,2), (2,1),
    (0,2), (2,0),
    (0,1), (1,0),
    (0,4), (4,0),
    (0,5), (5,0),
    (4,1), (1,4),
    (2,5), (5,2),
    (0,3), (3,0),
    (1,3), (3,1),
    (4,2), (2,4),
    (4,3), (3,4),
    (4,6), (6,4)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We model an itinerary as a permutation of the 7 cities:
#   pos[i] : index of the city visited at itinerary position i, for i = 0, ..., 6.
#   S[i]   : arrival day (start day) for the city at position i.
#
# Constraints:
#   - S[0] = 1.
#   - For the first city, the effective stay is the full planned duration.
#   - For each subsequent city (i >= 1), effective stay = (planned duration - 1).
#   - The departure day from the last city must equal day 20.
#
# Note: Departure day is computed as:
#   For i = 0: S[0] + durations[city] - 1.
#   For i >= 1: S[i] + (durations[city] - 1) - 1.
# -----------------------------------------------------------------------------

n = 7
s = Solver()

# Define the itinerary as a permutation.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Define arrival day vector.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1: S[1] = S[0] + (full planned duration of city at pos[0]).
# For positions i >= 2: S[i] = S[i-1] + (duration of city at pos[i-1] - 1).
# -----------------------------------------------------------------------------

# Position 1:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    If(pos[0] == 4, durations[4],
    If(pos[0] == 5, durations[5],
    /* pos[0] == 6 */ durations[6]))))))
)

# For positions 2 to n-1:
for i in range(2, n):
    s.add(
        S_days[i] ==
        S_days[i-1] +
        If(pos[i-1] == 0, durations[0] - 1,
        If(pos[i-1] == 1, durations[1] - 1,
        If(pos[i-1] == 2, durations[2] - 1,
        If(pos[i-1] == 3, durations[3] - 1,
        If(pos[i-1] == 4, durations[4] - 1,
        If(pos[i-1] == 5, durations[5] - 1,
        /* pos[i-1]==6 */ durations[6] - 1))))))
    )

# Trip end constraint:
# For the last city (position n-1), effective stay = durations - 1 (since it's not the first city),
# so departure day = S_days[n-1] + (durations - 1) - 1 must equal 20.
last_eff = If(pos[n-1] == 0, durations[0] - 1,
           If(pos[n-1] == 1, durations[1] - 1,
           If(pos[n-1] == 2, durations[2] - 1,
           If(pos[n-1] == 3, durations[3] - 1,
           If(pos[n-1] == 4, durations[4] - 1,
           If(pos[n-1] == 5, durations[5] - 1,
           durations[6] - 1)))))
s.add(S_days[n-1] + last_eff - 1 == 20)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair of cities in the itinerary, there must be a direct flight.
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
# For a city with an event, if it is visited at itinerary position i, then its visit interval 
# (from arrival to departure) must overlap the event window.
#
# For the first city, interval = [S, S + durations[city] - 1].
# For subsequent cities, interval = [S, S + (durations[city] - 1) - 1] = [S, S + durations[city] - 2].
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
        # Compute effective stay: full duration if first city; else (duration - 1)
        effective = durations[city_index] if i == 0 else durations[city_index] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")