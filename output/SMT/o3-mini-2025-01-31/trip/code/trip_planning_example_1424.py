from z3 import Solver, Int, IntVector, Distinct, And, Or, If, sat

# Helper functions to convert day numbers to strings (optional)
def day_str(day):
    return f"Day {day}"

# Define city indices and their planned stay durations.
# City indices and durations:
# 0: Warsaw       -> 3 days
# 1: Porto        -> 5 days   (Workshop must be attended in Porto between day 1 and day 5)
# 2: Naples       -> 4 days   (Conference in Naples between day 17 and day 20)
# 3: Brussels     -> 3 days   (Annual show in Brussels from day 20 to day 22)
# 4: Split        -> 3 days
# 5: Reykjavik    -> 5 days
# 6: Amsterdam    -> 4 days   (Visit relatives in Amsterdam between day 5 and day 8)
# 7: Lyon         -> 3 days
# 8: Helsinki     -> 4 days   (Wedding in Helsinki between day 8 and day 11)
# 9: Valencia     -> 2 days

cities = ["Warsaw", "Porto", "Naples", "Brussels", "Split",
          "Reykjavik", "Amsterdam", "Lyon", "Helsinki", "Valencia"]

durations = [3, 5, 4, 3, 3, 5, 4, 3, 4, 2]

# Allowed direct flights (bidirectional)
allowed_flight_pairs = {
    (6, 0),   # Amsterdam - Warsaw
    (8, 3),   # Helsinki - Brussels
    (8, 0),   # Helsinki - Warsaw
    (5, 3),   # Reykjavik - Brussels
    (6, 7),   # Amsterdam - Lyon
    (6, 2),   # Amsterdam - Naples
    (6, 5),   # Amsterdam - Reykjavik
    (2, 9),   # Naples - Valencia
    (1, 3),   # Porto - Brussels
    (6, 4),   # Amsterdam - Split
    (7, 4),   # Lyon - Split
    (0, 4),   # Warsaw - Split
    (1, 6),   # Porto - Amsterdam
    (8, 4),   # Helsinki - Split
    (3, 7),   # Brussels - Lyon
    (1, 7),   # Porto - Lyon
    (5, 0),   # Reykjavik - Warsaw
    (3, 9),   # Brussels - Valencia
    (9, 7),   # Valencia - Lyon
    (1, 0),   # Porto - Warsaw
    (0, 9),   # Warsaw - Valencia
    (6, 8),   # Amsterdam - Helsinki
    (1, 9),   # Porto - Valencia
    (0, 3),   # Warsaw - Brussels
    (0, 2),   # Warsaw - Naples
    (2, 4),   # Naples - Split
    (8, 2),   # Helsinki - Naples
    (8, 5),   # Helsinki - Reykjavik
    (6, 9),   # Amsterdam - Valencia
    (2, 3)    # Naples - Brussels
}

def flight_allowed(a, b):
    return ((a, b) in allowed_flight_pairs) or ((b, a) in allowed_flight_pairs)

# Total trip length is 27 days.
# Interpretation:
# - For the first city visited, you spend its full planned duration.
# - For every subsequent city, the flight takes 1 day, so the effective stay is (planned duration - 1).
# Therefore the total trip length is:
#    total_days = durations[first] + sum_{i>=1}(durations[i] - 1)
# With 10 cities, this is: sum(durations) - 9 = 27.
# (Indeed: sum(durations)=36, 36-9=27.)

n = 10  # number of cities to visit

# Create solver
s = Solver()

# Decision variables:
# pos[i] will represent the city visited at position i (0-indexed, positions 0..9)
pos = IntVector('pos', n)
# They should form a permutation of {0,...,9}
s.add(Distinct(pos))
for i in range(n):
    s.add(And(pos[i] >= 0, pos[i] < 10))

# Arrival day variables: S[i] is the day on which you arrive at the city in pos[i].
S = IntVector('S', n)
# Trip starts on day 1.
s.add(S[0] == 1)
for i in range(n):
    s.add(S[i] >= 1)

# Define the sequential arrival days.
# For the first city, you spend its full planned duration.
# For i = 1, S[1] = S[0] + duration(pos[0]).
# For i >= 2, S[i] = S[i-1] + (duration(pos[i-1]) - 1) because you spend one day traveling.
# Note: durations depend on the city chosen at that position, so we use nested If expressions.

# For position 1:
s.add(
    S[1] ==
    If(pos[0] == 0, durations[0],
    If(pos[0] == 1, durations[1],
    If(pos[0] == 2, durations[2],
    If(pos[0] == 3, durations[3],
    If(pos[0] == 4, durations[4],
    If(pos[0] == 5, durations[5],
    If(pos[0] == 6, durations[6],
    If(pos[0] == 7, durations[7],
    If(pos[0] == 8, durations[8],
    /* else: */ durations[9]))))))))

# For positions i = 2 to 9:
for i in range(2, n):
    s.add(
        S[i] == S[i-1] +
        If(pos[i-1] == 0, durations[0] - 1,
        If(pos[i-1] == 1, durations[1] - 1,
        If(pos[i-1] == 2, durations[2] - 1,
        If(pos[i-1] == 3, durations[3] - 1,
        If(pos[i-1] == 4, durations[4] - 1,
        If(pos[i-1] == 5, durations[5] - 1,
        If(pos[i-1] == 6, durations[6] - 1,
        If(pos[i-1] == 7, durations[7] - 1,
        If(pos[i-1] == 8, durations[8] - 1,
        /* else: */ durations[9] - 1)))))))))

# The trip ends on day 27.
# The departure day from the last city is:
# trip_end = S[n-1] + (duration(pos[n-1]) - 1)
trip_end = Int("trip_end")
trip_end_expr = If(pos[n-1] == 0, durations[0] - 1,
                If(pos[n-1] == 1, durations[1] - 1,
                If(pos[n-1] == 2, durations[2] - 1,
                If(pos[n-1] == 3, durations[3] - 1,
                If(pos[n-1] == 4, durations[4] - 1,
                If(pos[n-1] == 5, durations[5] - 1,
                If(pos[n-1] == 6, durations[6] - 1,
                If(pos[n-1] == 7, durations[7] - 1,
                If(pos[n-1] == 8, durations[8] - 1,
                /* else: */ durations[9] - 1)))))))))
s.add(trip_end == S[n-1] + trip_end_expr)
s.add(trip_end == 27)

# Flight connectivity constraints:
# For each consecutive pair in the itinerary, there must be a direct flight.
for i in range(n - 1):
    connections = []
    # For every possible pair of cities (a, b) that are connected, add the condition.
    for a in range(10):
        for b in range(10):
            if flight_allowed(a, b):
                connections.append(And(pos[i] == a, pos[i+1] == b))
    s.add(Or(connections))

# Event constraints:

# 1. Workshop in Porto between day 1 and day 5.
# Porto has index 1 and its planned duration is 5 days, so its effective interval is [S, S+4].
# To attend the workshop, we require the Porto visit to start early enough such that S <= 5.
for i in range(n):
    s.add(If(pos[i] == 1, S[i] <= 5, True))

# 2. Conference in Naples between day 17 and day 20.
# Naples: index 2, duration 4 => effective interval [S, S+3].
# To cover the event, we require that the visit covers at least one day from day 17 to day 20:
# We enforce S <= 20 and S+3 >= 17.
for i in range(n):
    s.add(If(pos[i] == 2, And(S[i] <= 20, S[i] + 3 >= 17), True))

# 3. Annual show in Brussels from day 20 to day 22.
# Brussels: index 3, duration 3 => effective interval [S, S+2].
# Require that S <= 22 and S+2 >= 20.
for i in range(n):
    s.add(If(pos[i] == 3, And(S[i] <= 22, S[i] + 2 >= 20), True))

# 4. Visit relatives in Amsterdam between day 5 and day 8.
# Amsterdam: index 6, duration 4 => effective interval [S, S+3].
# We require S <= 8 (ensuring the visit occurs early enough).
for i in range(n):
    s.add(If(pos[i] == 6, S[i] <= 8, True))

# 5. Wedding in Helsinki between day 8 and day 11.
# Helsinki: index 8, duration 4 => effective interval [S, S+3].
# We require S <= 11.
for i in range(n):
    s.add(If(pos[i] == 8, S[i] <= 11, True))

# Now attempt to solve the model
if s.check() == sat:
    m = s.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrival_days = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city = cities[itinerary[i]]
        # Calculate effective duration: first city uses full duration; subsequent cities lose 1 day for the flight.
        eff_duration = durations[itinerary[i]] if i == 0 else durations[itinerary[i]] - 1
        departure_day = arrival_days[i] + eff_duration - 1
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrival_days[i]:2d} | Departure: Day {departure_day:2d}")
    print(f"Trip ends on day: {m.evaluate(trip_end)}")
else:
    print("No valid trip plan could be found.")