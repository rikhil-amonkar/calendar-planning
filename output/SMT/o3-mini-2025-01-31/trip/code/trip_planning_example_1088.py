from z3 import Solver, Int, IntVector, Distinct, And, Or, If, sat

# Define city indices and durations.
# Cities: 0: Oslo, 1: Stuttgart, 2: Reykjavik, 3: Split, 4: Geneva, 5: Porto, 6: Tallinn, 7: Stockholm
cities = ["Oslo", "Stuttgart", "Reykjavik", "Split", "Geneva", "Porto", "Tallinn", "Stockholm"]
durations = [5, 5, 2, 3, 2, 3, 5, 3]  # planned stay durations in the city (if visited first, full days; subsequent visits lose 1 day for travel)

# Allowed direct flights (undirected) given as pairs of city indices.
# (A, B) means there is a flight between city A and city B.
allowed_flight_pairs = {
    (2, 1),   # Reykjavik - Stuttgart
    (2, 7),   # Reykjavik - Stockholm
    (2, 6),   # Reykjavik - Tallinn
    (7, 0),   # Stockholm - Oslo
    (1, 5),   # Stuttgart - Porto
    (0, 3),   # Oslo - Split
    (7, 1),   # Stockholm - Stuttgart
    (2, 0),   # Reykjavik - Oslo
    (0, 4),   # Oslo - Geneva
    (7, 3),   # Stockholm - Split
    (3, 1),   # Split - Stuttgart
    (6, 0),   # Tallinn - Oslo
    (7, 4),   # Stockholm - Geneva
    (0, 5),   # Oslo - Porto
    (4, 5),   # Geneva - Porto
    (4, 3)    # Geneva - Split
}
# Because flights are undirected, we consider both orders.
def flight_allowed(a, b):
    return ((a, b) in allowed_flight_pairs) or ((b, a) in allowed_flight_pairs)

# Total trip length is 21 days.
# Interpretation: When you start the trip in the first city, you spend the full city duration.
# On every subsequent city you lose one day (the flight day).
# Therefore, if the cities are visited in order c0, c1, ..., c7, then:
#   Total_days = durations[c0] + sum_{i=1..7} (durations[c_i] - 1) = 21.
# Given the durations, note that:
#   durations[c0] + sum_{i=1..7}(durations[c_i]) - 7 = 21  ==> sum_{i=0..7} durations[c_i] = 28.
# This will be automatically enforced by our sequential scheduling.

# We set up variables for the itinerary.
n = 8  # 8 cities

# pos[i]: the city index visited at position i (0-indexed positions: 0,...,7).
pos = IntVector('pos', n)
# The itinerary must be a permutation of [0,...,7].
s = Solver()
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < 8))

# Constraint: The conference in Reykjavik on day 1 and day 2 forces Reykjavik as the first city.
# Reykjavik has index 2.
s.add(pos[0] == 2)

# We define arrival day variables for each city in the itinerary.
# S[i] is the day (from 1 to 21) on which you arrive at city pos[i].
S = IntVector('S', n)
# The trip starts on day 1 at the first city.
s.add(S[0] == 1)

# For the first city, you spend the full duration.
# For subsequent cities (i >= 1), you depart previous city and (because flights are taken in the morning)
# you effectively lose 1 day from the visited duration.
# So, for i == 1: arrival day S[1] = S[0] + durations[pos[0]].
# For i >= 2: S[i] = S[i-1] + (durations[pos[i-1]] - 1).
# However, durations depend on the city chosen at that position.
# We encode these sequential constraints using If.
s.add(S[1] == S[0] + durations[2])  # pos[0] is fixed as Reykjavik, durations[2] = 2.
for i in range(2, n):
    # S[i] = S[i-1] + (durations of city at pos[i-1] minus 1)
    # We use a helper: for each possible city k, if pos[i-1] == k then add durations[k]-1.
    s.add(S[i] == S[i-1] + 
          If(pos[i-1] == 0, durations[0]-1,
          If(pos[i-1] == 1, durations[1]-1,
          If(pos[i-1] == 2, durations[2]-1,
          If(pos[i-1] == 3, durations[3]-1,
          If(pos[i-1] == 4, durations[4]-1,
          If(pos[i-1] == 5, durations[5]-1,
          If(pos[i-1] == 6, durations[6]-1,
          /* else: */ durations[7]-1)))))))

# The trip must end on day 21.
# That is, the departure from the last city is after spending the effective days.
# For the last city at position n-1, effective duration is:
#   if n-1 == 0 then full duration else (duration-1).
# Here, pos[0] is Reykjavik which we already did.
# For pos[n-1], the trip end day = S[n-1] + (durations[pos[n-1]] - 1).
trip_end = Int("trip_end")
trip_end_expr = 0
# Because n-1 >= 1 always, we use: trip_end = S[n-1] + (duration(pos[n-1]) - 1).
trip_end_expr = S[n-1] + (
                 If(pos[n-1] == 0, durations[0]-1,
                 If(pos[n-1] == 1, durations[1]-1,
                 If(pos[n-1] == 2, durations[2]-1,
                 If(pos[n-1] == 3, durations[3]-1,
                 If(pos[n-1] == 4, durations[4]-1,
                 If(pos[n-1] == 5, durations[5]-1,
                 If(pos[n-1] == 6, durations[6]-1,
                 /* else: */ durations[7]-1)))))))
s.add(trip_end == trip_end_expr)
s.add(trip_end == 21)

# Flight connectivity constraints:
# For every consecutive pair in the itinerary, there must be a direct flight between the two cities.
for i in range(n-1):
    # We need: flight_allowed(pos[i], pos[i+1]) is True.
    # We encode this by enumerating all possibilities.
    conn = []
    for a in range(8):
        for b in range(8):
            if flight_allowed(a, b):
                conn.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(conn))
    
# Event constraints:

# 1. Conference in Reykjavik on day 1 and day 2.
#    Already enforced by forcing Reykjavik as the first city and S[0] == 1. (Reykjavik duration is 2 days.)

# 2. Workshop in Porto between day 19 and day 21.
#    Porto has index 5 and duration 3. If Porto is visited at position i (i>=1 since pos[0] is fixed),
#    then its effective visit spans from S[i] to S[i] + (3 - 1) = S[i] + 2.
#    To have the workshop between day 19 and day 21 we require
#         S[i] <= 21   and   S[i] + 2 >= 19.
for i in range(1, n):
    s.add(If(pos[i] == 5, And(S[i] <= 21, S[i] + 2 >= 19), True))

# 3. Meeting a friend in Stockholm between day 2 and day 4.
#    Stockholm has index 7 and duration 3. For a visit at position i (if i>=1 then effective duration is 2 days)
#    so the effective interval is [S[i], S[i]+2]. To intersect [2,4] we require S[i] <= 4.
for i in range(n):
    s.add(If(pos[i] == 7, S[i] <= 4, True))

# (Optional) To help the solver, we know the trip must use the durations in some order such that
# the total sum equals: durations[pos[0]] + sum_{i=1..7}(durations[pos[i]] - 1) = 21.
# This is automatically enforced by our S and trip_end constraints.

# Now check for a solution.
if s.check() == sat:
    m = s.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrival_days = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary (positions 0 to 7):")
    for i in range(n):
        city = cities[itinerary[i]]
        # Compute effective duration: first city full, subsequent cities lose 1 day.
        eff_duration = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        depart_day = arrival_days[i] + eff_duration - 1
        print(f" Position {i+1}: {city} (Arrival day: {arrival_days[i]}, Departure day: {depart_day})")
    print(f"Trip end day: {m.evaluate(trip_end)}")
else:
    print("No valid trip plan could be found.")