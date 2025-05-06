from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 7 cities with the following properties:
# 0: Mykonos  - 3 days, with a wedding that must occur between day 4 and day 6.
#                 For its 3-day visit [S, S+2], require S <= 6 and S+2 >= 4.
# 1: Riga     - 3 days, no special event.
# 2: Munich   - 4 days, no special event.
# 3: Bucharest- 4 days, no special event.
# 4: Rome     - 4 days, with a conference that must cover day 1 and day 4.
#                 For its 4-day visit [S, S+3], since the trip cannot start before day 1,
#                 we force S == 1.
# 5: Nice     - 3 days, no special event.
# 6: Krakow   - 2 days, with an annual show that must occur from day 16 to day 17.
#                 For its 2-day visit [S, S+1], we require S == 16.
#
# Total durations = 3 + 3 + 4 + 4 + 4 + 3 + 2 = 23.
# There are 6 flights between the 7 cities (each flight overlaps one day).
# Hence the effective trip length is 23 - 6 = 17 days.
# The departure day from the last city must equal 17.

n = 7
total_trip = 17
cities = ["Mykonos", "Riga", "Munich", "Bucharest", "Rome", "Nice", "Krakow"]
durations = [3, 3, 4, 4, 4, 3, 2]

solver = Solver()

# Decision variables:
# pos[i] will represent the index of the city visited at position i.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] represents the arrival (start) day for the city in position i.
# The trip starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain the arrival times:
# When you finish the stay at the city in position i-1 (i.e. spending its full duration),
# you take a flight that overlaps the final day.
# Hence, for i>=1: S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights between consecutive cities.
# City indices:
# 0: Mykonos, 1: Riga, 2: Munich, 3: Bucharest, 4: Rome, 5: Nice, 6: Krakow.
#
# The allowed flights are given as follows:
# - Nice and Riga            : (5,1) and (1,5)
# - Bucharest and Munich     : (3,2) and (2,3)
# - Mykonos and Munich       : (0,2) and (2,0)
# - Riga and Bucharest       : (1,3) and (3,1)
# - Rome and Nice            : (4,5) and (5,4)
# - Rome and Munich          : (4,2) and (2,4)
# - Mykonos and Nice         : (0,5) and (5,0)
# - Rome and Mykonos         : (4,0) and (0,4)
# - Munich and Krakow        : (2,6) and (6,2)
# - Rome and Bucharest       : (4,3) and (3,4)
# - Nice and Munich          : (5,2) and (2,5)
# - from Riga to Munich      : (1,2)  [unidirectional]
# - from Rome to Riga        : (4,1)  [unidirectional]

allowed_flights = {
    (5,1), (1,5),
    (3,2), (2,3),
    (0,2), (2,0),
    (1,3), (3,1),
    (4,5), (5,4),
    (4,2), (2,4),
    (0,5), (5,0),
    (4,0), (0,4),
    (2,6), (6,2),
    (4,3), (3,4),
    (5,2), (2,5),
    (1,2),  # Riga -> Munich (unidirectional)
    (4,1)   # Rome -> Riga (unidirectional)
}

for i in range(n - 1):
    opts = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                opts.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(opts))

# Special event constraints:
for i in range(n):
    # Mykonos (city 0): Wedding between day 4 and day 6.
    # For a 3-day visit [S, S+2], require: S <= 6 and S+2 >= 4.
    solver.add(If(pos[i] == 0, And(S[i] <= 6, S[i] + 2 >= 4), True))
    
    # Rome (city 4): Conference on day 1 and day 4.
    # For a 4-day visit [S, S+3], to include day 1 and day 4 we need S == 1.
    solver.add(If(pos[i] == 4, S[i] == 1, True))
    
    # Krakow (city 6): Annual show from day 16 to day 17.
    # For a 2-day visit [S, S+1], require S == 16.
    solver.add(If(pos[i] == 6, S[i] == 16, True))

# -----------------------------------------------------------------------------
# Solve the model.
# -----------------------------------------------------------------------------
if solver.check() == sat:
    m = solver.model()
    itinerary = [m.evaluate(pos[i]).as_long() for i in range(n)]
    arrivals  = [m.evaluate(S[i]).as_long() for i in range(n)]
    
    print("Trip Itinerary:")
    for i in range(n):
        city_index = itinerary[i]
        city = cities[city_index]
        arrival = arrivals[i]
        departure = arrival + durations[city_index] - 1
        print(f" Position {i+1}: {city:10s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    
    final_day = m.evaluate(S[n-1] + durations[itinerary[-1]] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")