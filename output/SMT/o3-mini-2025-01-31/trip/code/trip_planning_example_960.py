from z3 import *

# Cities with indices, durations and event constraints:
# 0: Munich   (4 days) – Workshop in Munich between day 4 and 7 ⇒ force arrival = 4.
# 1: Vilnius  (2 days)
# 2: London   (2 days)
# 3: Venice   (3 days) – Conference in Venice between day 2 and 4 ⇒ force arrival = 2.
# 4: Brussels (4 days)
# 5: Tallinn  (5 days)
# 6: Florence (5 days)
#
# Total raw days = 4 + 2 + 2 + 3 + 4 + 5 + 5 = 25.
# With 6 transitions (shared days) the overall trip length = 25 - 6 = 19 days.
cities = ["Munich", "Vilnius", "London", "Venice", "Brussels", "Tallinn", "Florence"]
durations = [4, 2, 2, 3, 4, 5, 5]

# Allowed direct flights:
# 1. from Vilnius to Munich               => one-way: (Vilnius, Munich) : (1, 0)
# 2. from Tallinn to Vilnius              => one-way: (Tallinn, Vilnius) : (5, 1)
# 3. Vilnius and Brussels                => bidir: (Vilnius, Brussels) : (1, 4)
# 4. Venice and Munich                   => bidir: (Venice, Munich) : (3, 0)
# 5. Munich and Tallinn                  => bidir: (Munich, Tallinn) : (0, 5)
# 6. London and Florence                 => bidir: (London, Florence) : (2, 6)
# 7. London and Brussels                 => bidir: (London, Brussels) : (2, 4)
# 8. London and Venice                   => bidir: (London, Venice) : (2, 3)
# 9. London and Munich                   => bidir: (London, Munich) : (2, 0)
# 10. Brussels and Florence              => bidir: (Brussels, Florence) : (4, 6)
# 11. Tallinn and Brussels               => bidir: (Tallinn, Brussels) : (5, 4)
# 12. from Florence to Munich            => one-way: (Florence, Munich) : (6, 0)
# 13. Venice and Brussels                => bidir: (Venice, Brussels) : (3, 4)
# 14. Munich and Brussels                => bidir: (Munich, Brussels) : (0, 4)
allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. One-way: Vilnius -> Munich
allowed_flights.append((1, 0))
# 2. One-way: Tallinn -> Vilnius
allowed_flights.append((5, 1))
# 3. Vilnius <-> Brussels
bidir(1, 4)
# 4. Venice <-> Munich
bidir(3, 0)
# 5. Munich <-> Tallinn
bidir(0, 5)
# 6. London <-> Florence
bidir(2, 6)
# 7. London <-> Brussels
bidir(2, 4)
# 8. London <-> Venice
bidir(2, 3)
# 9. London <-> Munich
bidir(2, 0)
# 10. Brussels <-> Florence
bidir(4, 6)
# 11. Tallinn <-> Brussels
bidir(5, 4)
# 12. One-way: Florence -> Munich
allowed_flights.append((6, 0))
# 13. Venice <-> Brussels
bidir(3, 4)
# 14. Munich <-> Brussels
bidir(0, 4)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the visitation order as a permutation of city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# Trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit, departure = arrival + (duration - 1)
for i in range(n):
    s.add(
        Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
            for c in range(n)])
    )

# Consecutive visits share a transit day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 19.
s.add(departures[n-1] == 19)

# Event-specific constraints:
# Munich (city 0): workshop between day 4 and 7  ⇒ force arrival = 4.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 4, True))
# Venice (city 3): conference between day 2 and 4 ⇒ force arrival = 2.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 2, True))

# Connectivity constraints:
# For every consecutive pair in the itinerary, a direct flight must exist.
for i in range(n - 1):
    direct_flight = []
    for (frm, to) in allowed_flights:
        direct_flight.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*direct_flight))

# Solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_idx]:10s}: [{a_day}, {d_day}]")
else:
    print("No solution found")