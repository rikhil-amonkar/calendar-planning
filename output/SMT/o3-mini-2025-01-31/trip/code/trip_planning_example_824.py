from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# 0: Berlin    – 5 days.
#      Event: Annual show in Berlin from day 1 to day 5.
# 1: Split     – 3 days.
# 2: Bucharest – 3 days.
#      Event: Visit relatives in Bucharest between day 13 and day 15.
# 3: Riga      – 5 days.
# 4: Lisbon    – 3 days.
# 5: Tallinn   – 4 days.
# 6: Lyon      – 5 days.
#      Event: Wedding in Lyon between day 7 and day 11.
#
# Total planned days = 5 + 3 + 3 + 5 + 3 + 4 + 5 = 28.
# There are 6 flight transitions, so effective trip duration = 28 - 6 = 22 days.
#
# Notes:
#  - The trip starts on day 1.
#  - For the first visited city you use the full planned duration.
#  - For each subsequent city, one day is lost due to the flight (effective stay = planned - 1).
# -----------------------------------------------------------------------------

cities    = ["Berlin", "Split", "Bucharest", "Riga", "Lisbon", "Tallinn", "Lyon"]
durations = [5,        3,       3,         5,     3,       4,        5]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    0: (1, 5),    # Berlin: annual show from day 1 to day 5.
    2: (13,15),   # Bucharest: visit relatives between day 13 and day 15.
    6: (7,11)     # Lyon: wedding between day 7 and day 11.
}

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional):
#
# Provided pairs:
# - Lisbon and Bucharest   -> (4,2) and (2,4)
# - Berlin and Lisbon      -> (0,4) and (4,0)
# - Bucharest and Riga     -> (2,3) and (3,2)
# - Berlin and Riga        -> (0,3) and (3,0)
# - Split and Lyon         -> (1,6) and (6,1)
# - Lisbon and Riga        -> (4,3) and (3,4)
# - Riga and Tallinn       -> (3,5) and (5,3)   # "from Riga to Tallinn"
# - Berlin and Split       -> (0,1) and (1,0)
# - Lyon and Lisbon        -> (6,4) and (4,6)
# - Berlin and Tallinn     -> (0,5) and (5,0)
# - Lyon and Bucharest     -> (6,2) and (2,6)
# -----------------------------------------------------------------------------

allowed_flights = {
    (4,2), (2,4),
    (0,4), (4,0),
    (2,3), (3,2),
    (0,3), (3,0),
    (1,6), (6,1),
    (4,3), (3,4),
    (3,5), (5,3),
    (0,1), (1,0),
    (6,4), (4,6),
    (0,5), (5,0),
    (6,2), (2,6)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and decision variables.
#
# We assume an itinerary of 7 cities (a permutation of indices 0..6):
#   pos[i]   : the city index visited at itinerary position i.
#   S[i]     : the arrival day for the city at position i.
#
# Constraints:
#   S[0] = 1.
#   For position 1: S[1] = S[0] + (the full duration of the city at pos[0]).
#   For positions i >= 2: S[i] = S[i-1] + (duration(city at pos[i-1]) - 1).
#   Trip end: For the last city, departure day (arrival + effective stay - 1)
#             must equal day 22.
# -----------------------------------------------------------------------------

n = 7
s = Solver()

# Itinerary: permutation of indices 0...6.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector (S).
S_days = IntVector("S", n)
s.add(S_days[0] == 1)  # The trip starts on day 1.
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# For the first city, the full duration is used.
# For each subsequent city, one day is lost due to the flight.
# -----------------------------------------------------------------------------

# For the first transition (position 1):
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
        /* pos[i-1] == 6 */ durations[6] - 1))))))
    )

# Trip end constraint:
# For the last city (position n-1), effective stay = (duration - 1), and the departure day is:
#   S_days[n-1] + (duration(last city) - 1) - 1 = 22.
last_eff = If(pos[n-1] == 0, durations[0] - 1,
           If(pos[n-1] == 1, durations[1] - 1,
           If(pos[n-1] == 2, durations[2] - 1,
           If(pos[n-1] == 3, durations[3] - 1,
           If(pos[n-1] == 4, durations[4] - 1,
           If(pos[n-1] == 5, durations[5] - 1,
           durations[6] - 1)))))
s.add(S_days[n-1] + last_eff - 1 == 22)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair in the itinerary, a direct flight must exist.
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
# For each city with an event, if that city is visited at position i, then the visit
# interval [S_days[i], S_days[i] + effective - 1] (where effective = full duration if i==0,
# else duration-1) must overlap the event window.
#
# That is:
#    S_days[i] <= event_end   and   (S_days[i] + effective - 1) >= event_start.
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
        city = itinerary[i]
        city_name = cities[city]
        # Effective stay: full duration for first city, (duration - 1) for subsequent cities.
        effective = durations[city] if i == 0 else durations[city] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:10s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")