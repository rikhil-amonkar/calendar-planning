from z3 import Solver, IntVector, Distinct, And, Or, If, Sum, sat

# We have 7 cities with the following properties:
# City indices and durations:
# 0: Vienna   - 4 days. Conference in Vienna must be attended on day 1 and day 4.
#              For a 4‑day visit [S, S+3] to include day 1 and day 4, we require S == 1.
# 1: Milan    - 2 days.
# 2: Rome     - 3 days.
# 3: Riga     - 2 days.
# 4: Lisbon   - 3 days. Relatives in Lisbon between day 11 and day 13.
#              For a 3‑day visit [S, S+2] to include some day in [11,13], we require S <= 13 and S+2 >= 11.
# 5: Vilnius  - 4 days.
# 6: Oslo     - 3 days. Meeting a friend in Oslo between day 13 and day 15.
#              For a 3‑day visit [S, S+2] to include a day in [13,15], we require S <= 15 and S+2 >= 13.
#
# Total durations = 4 + 2 + 3 + 2 + 3 + 4 + 3 = 21 days.
# There are 6 flights (each flight overlaps the last day of the previous stay),
# so the effective trip length = 21 - 6 = 15 days.
# Hence, the departure day from the final city must be day 15.

cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
durations = [4, 2, 3, 2, 3, 4, 3]
n = len(cities)
total_trip = 15

solver = Solver()

# Decision variables:
# pos[i] represents the index of the city visited at position i.
# They form a permutation of {0,1,...,6}.
pos = IntVector("pos", n)
solver.add(Distinct(pos))
for i in range(n):
    solver.add(And(pos[i] >= 0, pos[i] < n))

# S[i] is the arrival (start) day for the city visited at position i.
# The trip always starts on day 1.
S = IntVector("S", n)
solver.add(S[0] == 1)
for i in range(n):
    solver.add(S[i] >= 1)

# Chain the arrival times.
# After a city's stay, you catch a flight that overlaps the final day of that stay.
# Thus, for i>=1: S[i] = S[i-1] + (duration(city at pos[i-1]) - 1)
for i in range(1, n):
    solver.add(S[i] == S[i-1] + Sum([If(pos[i-1] == c, durations[c] - 1, 0) for c in range(n)]))

# The departure day from the last city must equal total_trip.
solver.add(S[n-1] + Sum([If(pos[n-1] == c, durations[c] - 1, 0) for c in range(n)]) == total_trip)

# Allowed direct flights between consecutive cities.
# City indices:
# 0: Vienna, 1: Milan, 2: Rome, 3: Riga, 4: Lisbon, 5: Vilnius, 6: Oslo.
#
# Allowed flights given (with bidirectional edges unless noted as "from" meaning one-way):
allowed_flights = {
    # Riga and Oslo
    (3,6), (6,3),
    # Rome and Oslo
    (2,6), (6,2),
    # Vienna and Milan
    (0,1), (1,0),
    # Vienna and Vilnius
    (0,5), (5,0),
    # Vienna and Lisbon
    (0,4), (4,0),
    # Riga and Milan
    (3,1), (1,3),
    # Lisbon and Oslo
    (4,6), (6,4),
    # from Rome to Riga (one-way from Rome to Riga)
    (2,3),
    # Rome and Lisbon
    (2,4), (4,2),
    # Vienna and Riga
    (0,3), (3,0),
    # Vienna and Rome
    (0,2), (2,0),
    # Milan and Oslo
    (1,6), (6,1),
    # Vienna and Oslo
    (0,6), (6,0),
    # Vilnius and Oslo
    (5,6), (6,5),
    # from Riga to Vilnius (one-way from Riga to Vilnius)
    (3,5),
    # Vilnius and Milan
    (5,1), (1,5),
    # Riga and Lisbon
    (3,4), (4,3),
    # Milan and Lisbon
    (1,4), (4,1)
}

for i in range(n-1):
    flight_options = []
    for a in range(n):
        for b in range(n):
            if (a, b) in allowed_flights:
                flight_options.append(And(pos[i] == a, pos[i+1] == b))
    solver.add(Or(flight_options))

# Special event constraints:
for i in range(n):
    # In Vienna (index 0): conference on day 1 and day 4 => S must equal 1.
    solver.add(If(pos[i] == 0, S[i] == 1, True))
    # In Lisbon (index 4): relatives visit between day 11 and day 13.
    solver.add(If(pos[i] == 4, And(S[i] <= 13, S[i] + 2 >= 11), True))
    # In Oslo (index 6): friend meeting between day 13 and day 15.
    solver.add(If(pos[i] == 6, And(S[i] <= 15, S[i] + 2 >= 13), True))

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
        print(f" Position {i+1}: {city:8s} | Arrival: Day {arrival:2d} | Departure: Day {departure:2d}")
    
    final_day = m.evaluate(S[n-1] + durations[ itinerary[-1] ] - 1)
    print("Trip ends on Day:", final_day)
else:
    print("No valid trip plan could be found.")