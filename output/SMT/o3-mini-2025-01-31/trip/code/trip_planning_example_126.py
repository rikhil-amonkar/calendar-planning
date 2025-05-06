from z3 import Solver, IntVector, Distinct, And, Or, If, sat

# -----------------------------------------------------------------------------
# City definitions and planned durations:
#
# 0: Seville  – 6 days.
# 1: Paris    – 2 days.
# 2: Krakow   – 5 days.
#      Event: Workshop in Krakow between day 1 and day 5.
#
# Total planned days = 6 + 2 + 5 = 13.
# There are 2 flight transitions so effective trip duration = 13 - 2 = 11 days.
#
# Note:
# - In the first visited city you use the full planned duration.
# - For subsequent cities the effective stay is (planned duration - 1),
#   since one day is spent flying.
# -----------------------------------------------------------------------------

cities    = ["Seville", "Paris", "Krakow"]
durations = [6,         2,       5]

# Event windows: mapping city index -> (event_start, event_end)
events = {
    2: (1, 5)  # Krakow: workshop between day 1 and day 5.
}

# -----------------------------------------------------------------------------
# Allowed direct flights (bidirectional):
#
# Provided pairs:
# - Krakow and Paris   -> (2,1) and (1,2)
# - Paris and Seville  -> (1,0) and (0,1)
# -----------------------------------------------------------------------------

allowed_flights = {
    (2, 1), (1, 2),
    (1, 0), (0, 1)
}

def flight_allowed(a, b):
    return (a, b) in allowed_flights

# -----------------------------------------------------------------------------
# Create the Z3 solver and declare decision variables.
#
# We assume the itinerary is a permutation of the 3 cities:
#   pos[i] is the city index visited in the ith position (i=0,1,2).
#   S[i] is the arrival day at the city visited at position i.
#
# Constraints:
#   S[0] = 1.
#   S[1] = S[0] + (duration of city at pos[0]), and 
#   For i>=2, S[i] = S[i-1] + (duration of city at pos[i-1] - 1).
#   Trip end: Departure day from the last city must equal day 11, i.e.
#     S[2] + (duration(pos[2]) - 1) - 1 = 11.
# -----------------------------------------------------------------------------

n = 3
s = Solver()

# Itinerary is a permutation of {0, 1, 2}.
pos = IntVector("pos", n)
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < n))

# Arrival days vector.
S_days = IntVector("S", n)
s.add(S_days[0] == 1)
for i in range(n):
    s.add(S_days[i] >= 1)

# -----------------------------------------------------------------------------
# Sequential arrival constraints:
#
# If the city at position i is the first one visited, then you stay its full 
# planned duration. Otherwise, you lose one day due to the flight.
# -----------------------------------------------------------------------------

# For the first transition: position 1.
s.add(
    S_days[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    /* pos[0] == 2 */ durations[2]))
)

# For positions i >= 2 (here only i == 2):
s.add(
    S_days[2] ==
    S_days[1] +
    If(pos[1] == 0, durations[0] - 1,
    If(pos[1] == 1, durations[1] - 1,
    /* pos[1] == 2 */ durations[2] - 1))
)

# Trip end constraint:
# For the last city visited, effective stay = duration - 1.
last_effective = If(pos[n-1] == 0, durations[0] - 1,
                  If(pos[n-1] == 1, durations[1] - 1,
                  /* pos[n-1]==2 */ durations[2] - 1))
# Departure day from the last city = arrival day + effective stay - 1 must equal 11.
s.add(S_days[n-1] + last_effective - 1 == 11)

# -----------------------------------------------------------------------------
# Flight connectivity constraints:
#
# For each consecutive pair of visited cities, a direct flight must exist.
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
# For any city with an event, if that city is visited at position i, the visit 
# interval (from arrival S_days[i] to S_days[i] + effective stay - 1) must overlap 
# with the event window.
#
# For the first city, effective stay = full planned duration.
# For later ones, effective stay = (duration - 1).
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
        effective = durations[city_index] if i == 0 else durations[city_index] - 1
        departure = arrivals[i] + effective - 1
        print(f" Position {i+1}: {city_name:7s} | Arrival: Day {arrivals[i]:2d} | Departure: Day {departure:2d}")
    trip_end = m.evaluate(S_days[n-1] + (durations[itinerary[n-1]] - 1) - 1)
    print("Trip ends on Day:", trip_end)
else:
    print("No valid trip plan could be found.")