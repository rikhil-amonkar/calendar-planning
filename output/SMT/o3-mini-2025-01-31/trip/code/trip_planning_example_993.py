from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 7 cities:
# 0: Riga      – 2 days.
# 1: Frankfurt – 3 days.
# 2: Amsterdam – 2 days.
#               Event: Meet a friend in Amsterdam between day 2 and day 3.
# 3: Vilnius   – 5 days.
#               Event: Attend a workshop in Vilnius between day 7 and day 11.
# 4: London    – 2 days.
# 5: Stockholm – 3 days.
#               Event: Attend a wedding in Stockholm between day 13 and day 15.
# 6: Bucharest – 4 days.
#
# Total planned days = 2 + 3 + 2 + 5 + 2 + 3 + 4 = 21.
# There are 6 flight transitions, so the effective trip duration = 21 - 6 = 15 days.
#
# Notes:
#  - The trip starts on day 1.
#  - In the first city, you enjoy its full planned duration.
#  - In every subsequent city one day is "lost" due to the flight.
# -----------------------------------------------------------------------------
cities    = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]
durations = [2,         3,           2,           5,        2,       3,          4]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    2: (2, 3),    # Amsterdam: meet friend between day 2 and day 3.
    3: (7, 11),   # Vilnius: workshop between day 7 and day 11.
    5: (13, 15)   # Stockholm: wedding between day 13 and day 15.
}

# -----------------------------------------------------------------------------
# Allowed direct flights:
#
# The allowed flights (as directed or bidirectional as noted) are:
#
# 1. London and Amsterdam      -> (London, Amsterdam) and (Amsterdam, London)
#       (4,2) and (2,4)
# 2. Vilnius and Frankfurt     -> (Vilnius, Frankfurt) and (Frankfurt, Vilnius)
#       (3,1) and (1,3)
# 3. from Riga to Vilnius       -> only (Riga, Vilnius)
#       (0,3)
# 4. Riga and Stockholm        -> (Riga, Stockholm) and (Stockholm, Riga)
#       (0,5) and (5,0)
# 5. London and Bucharest      -> (London, Bucharest) and (Bucharest, London)
#       (4,6) and (6,4)
# 6. Amsterdam and Stockholm   -> (Amsterdam, Stockholm) and (Stockholm, Amsterdam)
#       (2,5) and (5,2)
# 7. Amsterdam and Frankfurt   -> (Amsterdam, Frankfurt) and (Frankfurt, Amsterdam)
#       (2,1) and (1,2)
# 8. Frankfurt and Stockholm   -> (Frankfurt, Stockholm) and (Stockholm, Frankfurt)
#       (1,5) and (5,1)
# 9. Bucharest and Riga         -> (Bucharest, Riga) and (Riga, Bucharest)
#       (6,0) and (0,6)
#10. Amsterdam and Riga         -> (Amsterdam, Riga) and (Riga, Amsterdam)
#       (2,0) and (0,2)
#11. Amsterdam and Bucharest    -> (Amsterdam, Bucharest) and (Bucharest, Amsterdam)
#       (2,6) and (6,2)
#12. Riga and Frankfurt         -> (Riga, Frankfurt) and (Frankfurt, Riga)
#       (0,1) and (1,0)
#13. Bucharest and Frankfurt    -> (Bucharest, Frankfurt) and (Frankfurt, Bucharest)
#       (6,1) and (1,6)
#14. London and Frankfurt       -> (London, Frankfurt) and (Frankfurt, London)
#       (4,1) and (1,4)
#15. London and Stockholm       -> (London, Stockholm) and (Stockholm, London)
#       (4,5) and (5,4)
#16. Amsterdam and Vilnius      -> (Amsterdam, Vilnius) and (Vilnius, Amsterdam)
#       (2,3) and (3,2)
# -----------------------------------------------------------------------------
allowed_flights = {
    (4,2), (2,4),
    (3,1), (1,3),
    (0,3),  # from Riga to Vilnius (one-way)
    (0,5), (5,0),
    (4,6), (6,4),
    (2,5), (5,2),
    (2,1), (1,2),
    (1,5), (5,1),
    (6,0), (0,6),
    (2,0), (0,2),
    (2,6), (6,2),
    (0,1), (1,0),
    (6,1), (1,6),
    (4,1), (1,4),
    (4,5), (5,4),
    (2,3), (3,2)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We model the itinerary as an ordering (permutation) of the 7 cities:
#   pos[i] : index of the city visited at itinerary position i, for i = 0,...,6.
#   S[i]   : arrival day at the city visited at position i.
#
# When visiting a city:
#   - If it is the first city (i == 0): you enjoy its full planned duration.
#       Departure day = S[0] + durations[city] - 1.
#   - Otherwise (i >= 1): due to the flight, effective stay = (durations[city] - 1)
#         and departure day = S[i] + (durations[city] - 1) - 1.
#
# The departure day from the final city (position 6) must equal day 15.
# -----------------------------------------------------------------------------
n = 7
total_trip = 15
s = Solver()

# Itinerary positions as a permutation of the 7 cities.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#   S[1] = S[0] + full duration of the first visited city.
# For positions i>=2:
#   S[i] = S[i-1] + (duration of city at pos[i-1] - 1)
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
         durations[6])))))
)

# Positions 2 to 6:
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
            durations[6] - 1))))))
    )

# -----------------------------------------------------------------------------
# Trip end constraint:
#
# For the final city (position n-1), the effective departure day is:
#   departure = S_days[n-1] + (duration - 1) - 1
# and this must equal total_trip (15).
# -----------------------------------------------------------------------------
last_effective = If(pos[n-1] == 0, durations[0] - 1,
                If(pos[n-1] == 1, durations[1] - 1,
                If(pos[n-1] == 2, durations[2] - 1,
                If(pos[n-1] == 3, durations[3] - 1,
                If(pos[n-1] == 4, durations[4] - 1,
                If(pos[n-1] == 5, durations[5] - 1,
                     durations[6] - 1))))))
s.add(S_days[n-1] + last_effective - 1 == total_trip)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair in the itinerary (i to i+1),
# there must be a direct flight.
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
# For cities with events, if that city is visited at itinerary position i,
# then its visit interval must intersect the event window.
#
# Visit interval:
#   - If i == 0: [S[i], S[i] + durations - 1]
#   - If i >= 1: [S[i], S[i] + (durations - 1) - 1]
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