from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 7 cities:
# 0: Oslo       – 2 days.
#      Event: Meet friends at Oslo between day 3 and day 4.
# 1: Stuttgart  – 3 days.
# 2: Venice     – 4 days.
# 3: Split      – 4 days.
# 4: Barcelona  – 3 days.
#      Event: Annual show in Barcelona from day 1 to day 3.
# 5: Brussels   – 3 days.
#      Event: Meet a friend in Brussels between day 9 and day 11.
# 6: Copenhagen – 3 days.
#
# Total planned days = 2+3+4+4+3+3+3 = 22.
# There are 6 flights (transitions), so the effective trip duration = 22 - 6 = 16 days.
#
# Notes:
# - The trip starts on day 1.
# - In the first city you use its full planned duration.
# - In every subsequent city one day is lost to transit (effective stay = planned duration - 1).
# -----------------------------------------------------------------------------

cities    = ["Oslo", "Stuttgart", "Venice", "Split", "Barcelona", "Brussels", "Copenhagen"]
durations = [2,       3,          4,       4,       3,         3,         3]

# Events: mapping city index -> (event_start, event_end)
events = {
    0: (3, 4),   # Oslo: meet friends between day 3 and day 4.
    4: (1, 3),   # Barcelona: annual show between day 1 and day 3.
    5: (9, 11)   # Brussels: meet a friend between day 9 and day 11.
}

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# Provided pairs (bidirectional unless indicated):
#
# 1. Venice and Stuttgart      -> (2,1) and (1,2)
# 2. Oslo and Brussels         -> (0,5) and (5,0)
# 3. Split and Copenhagen      -> (3,6) and (6,3)
# 4. Barcelona and Copenhagen  -> (4,6) and (6,4)
# 5. Barcelona and Venice      -> (4,2) and (2,4)
# 6. Brussels and Venice       -> (5,2) and (2,5)
# 7. Barcelona and Stuttgart   -> (4,1) and (1,4)
# 8. Copenhagen and Brussels   -> (6,5) and (5,6)
# 9. Oslo and Split            -> (0,3) and (3,0)
#10. Oslo and Venice           -> (0,2) and (2,0)
#11. Barcelona and Split       -> (4,3) and (3,4)
#12. Oslo and Copenhagen       -> (0,6) and (6,0)
#13. Barcelona and Oslo        -> (4,0) and (0,4)
#14. Copenhagen and Stuttgart  -> (6,1) and (1,6)
#15. Split and Stuttgart       -> (3,1) and (1,3)
#16. Copenhagen and Venice     -> (6,2) and (2,6)
#17. Barcelona and Brussels    -> (4,5) and (5,4)
# -----------------------------------------------------------------------------

allowed_flights = {
    (2,1), (1,2),
    (0,5), (5,0),
    (3,6), (6,3),
    (4,6), (6,4),
    (4,2), (2,4),
    (5,2), (2,5),
    (4,1), (1,4),
    (6,5), (5,6),
    (0,3), (3,0),
    (0,2), (2,0),
    (4,3), (3,4),
    (0,6), (6,0),
    (4,0), (0,4),
    (6,1), (1,6),
    (3,1), (1,3),
    (6,2), (2,6),
    (4,5), (5,4)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We assume an itinerary ordering (a permutation) of the 7 cities:
#
#   pos[i] : the index of the city visited at itinerary position i (i=0,...,6)
#   S[i]   : the arrival day at the city visited at position i.
#
# Constraints:
#   - S[0] = 1.
#   - For the first city, the effective stay = full planned duration.
#   - For each subsequent city (i >= 1), effective stay = (planned duration - 1)
#   - Trip end: The departure day from the last city must equal day 16.
#
# The departure day for city at position i is:
#   if i == 0: S[i] + durations[city] - 1,
#   else: S[i] + (durations[city] - 1) - 1 = S[i] + durations[city] - 2.
# -----------------------------------------------------------------------------

n = 7
s = Solver()

# Itinerary as a permutation.
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
# For position 1: S[1] = S[0] + full duration of city at pos[0].
# For positions i>=2: S[i] = S[i-1] + (duration of city at pos[i-1] - 1).
# -----------------------------------------------------------------------------

# For position 1:
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    If(pos[0] == 4, durations[4],
    If(pos[0] == 5, durations[5],
    /* pos[0]==6 */ durations[6]))))))
)

# For positions 2 to n-1.
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
# For the last city (position n-1), effective stay = durations - 1 (since it is not the first city),
# so departure day = S_days[n-1] + (durations - 1) - 1 must equal 16.
last_eff = If(pos[n-1] == 0, durations[0] - 1,
           If(pos[n-1] == 1, durations[1] - 1,
           If(pos[n-1] == 2, durations[2] - 1,
           If(pos[n-1] == 3, durations[3] - 1,
           If(pos[n-1] == 4, durations[4] - 1,
           If(pos[n-1] == 5, durations[5] - 1,
           durations[6] - 1)))))
s.add(S_days[n-1] + last_eff - 1 == 16)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair in the itinerary, there must be a direct flight.
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
# For a city with an event, if it is visited at itinerary position i,
# then the visit interval (from arrival to departure) must overlap the event window.
#
# - For the first city, interval = [S, S + durations[city] - 1].
# - For subsequent cities, interval = [S, S + (durations[city] - 1) - 1] = [S, S + durations[city] - 2].
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
        # Calculate effective stay: full duration if first, else (duration - 1).
        effective = durations[city_index] if i == 0 else durations[city_index] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:12s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")