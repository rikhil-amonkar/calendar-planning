from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# We have 7 cities:
# 0: Stuttgart – 3 days.
#              Event: Workshop in Stuttgart between day 11 and day 13.
# 1: Edinburgh – 4 days.
# 2: Athens    – 4 days.
# 3: Split     – 2 days.
#              Event: Meet your friends at Split between day 13 and day 14.
# 4: Krakow   – 4 days.
#              Event: Meet a friend in Krakow between day 8 and day 11.
# 5: Venice   – 5 days.
# 6: Mykonos  – 4 days.
#
# Total planned days = 3+4+4+2+4+5+4 = 26.
# There are 6 flight transitions, so effective trip duration = 26 - 6 = 20 days.
#
# Note:
# - The trip starts on day 1 in the first city, where you enjoy its full planned duration.
# - In each subsequent city, one day is "lost" due to the flight (effective stay = duration - 1).
# -----------------------------------------------------------------------------
cities = ["Stuttgart", "Edinburgh", "Athens", "Split", "Krakow", "Venice", "Mykonos"]
durations = [3, 4, 4, 2, 4, 5, 4]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    0: (11, 13),  # Stuttgart: workshop between day 11 and 13.
    3: (13, 14),  # Split: meet friends between day 13 and 14.
    4: (8, 11)    # Krakow: meet a friend between day 8 and 11.
}

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional unless specified otherwise):
#
# 1. Krakow and Split      -> (4,3) and (3,4)
# 2. Split and Athens      -> (3,2) and (2,3)
# 3. Edinburgh and Krakow  -> (1,4) and (4,1)
# 4. Venice and Stuttgart  -> (5,0) and (0,5)
# 5. Krakow and Stuttgart  -> (4,0) and (0,4)
# 6. Edinburgh and Stuttgart-> (1,0) and (0,1)
# 7. Stuttgart and Athens   -> (0,2) and (2,0)
# 8. Venice and Edinburgh  -> (5,1) and (1,5)
# 9. Athens and Mykonos    -> (2,6) and (6,2)
# 10. Venice and Athens     -> (5,2) and (2,5)
# 11. Stuttgart and Split   -> (0,3) and (3,0)
# 12. Edinburgh and Athens  -> (1,2) and (2,1)
# -----------------------------------------------------------------------------
allowed_flights = {
    (4,3), (3,4),
    (3,2), (2,3),
    (1,4), (4,1),
    (5,0), (0,5),
    (4,0), (0,4),
    (1,0), (0,1),
    (0,2), (2,0),
    (5,1), (1,5),
    (2,6), (6,2),
    (5,2), (2,5),
    (0,3), (3,0),
    (1,2), (2,1)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We represent the itinerary as an ordering (permutation) of the 7 cities:
#   pos[i] : index of the city visited at itinerary position i (i = 0 ... 6).
#   S[i]   : arrival day at the city visited at itinerary position i.
#
# For the first city (i == 0): visit interval = [S, S + duration - 1].
# For every subsequent city (i >= 1): effective visit = (duration - 1) days,
#   so visit interval = [S, S + duration - 2].
#
# The departure day from the final city (position 6) must equal day 20.
# -----------------------------------------------------------------------------
n = 7
total_trip = 20
s = Solver()

# Itinerary as a permutation:
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days:
S = IntVector("S", n)
s.add(S[0] == 1)  # Trip starts on day 1.
for i in range(n):
    s.add(S[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For position 1:
#   S[1] = S[0] + (full duration of city at pos[0])
# For i >= 2:
#   S[i] = S[i-1] + ((duration at pos[i-1]) - 1)
# (Because from 2nd city onward, one day is lost due to the flight.)
# -----------------------------------------------------------------------------
s.add(
    S[1] ==
    S[0] +
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    If(pos[0] == 4, durations[4],
    If(pos[0] == 5, durations[5],
         durations[6])))))
)

for i in range(2, n):
    s.add(
        S[i] ==
        S[i-1] +
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
# For the final city (position n-1):
#   If not the first city, effective departure = S[n-1] + (duration - 1) - 1
#                                      = S[n-1] + duration - 2.
# This must equal total_trip.
# -----------------------------------------------------------------------------
s.add(
    S[n-1] +
    If(pos[n-1] == 0, durations[0] - 1,
    If(pos[n-1] == 1, durations[1] - 1,
    If(pos[n-1] == 2, durations[2] - 1,
    If(pos[n-1] == 3, durations[3] - 1,
    If(pos[n-1] == 4, durations[4] - 1,
    If(pos[n-1] == 5, durations[5] - 1,
         durations[6] - 1))))) - 1
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
# For each event city visited at itinerary position i, the visit interval must overlap
# with the event window. The visit interval is:
#   - For position 0: [S, S + duration - 1]
#   - For i >= 1:   [S, S + duration - 2]
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
    # Compute final trip end.
    final_city = itinerary[n-1]
    final_departure = arrivals[n-1] + (durations[final_city] - 1) - 1
    print("Trip ends on Day:", final_departure)
else:
    print("No valid trip plan could be found.")