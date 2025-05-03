from z3 import *

# Cities with durations and event constraints:
# 0: Mykonos    (3 days)
# 1: Manchester (4 days)
# 2: Dubrovnik  (4 days)
# 3: Vienna     (4 days)
# 4: Lisbon     (4 days) – Meet friend between day 6 and day 9 ⇒ force arrival = 6.
# 5: Riga       (3 days)
# 6: Dublin     (4 days) – Visit relatives between day 17 and day 20 ⇒ force arrival = 17.
#
# The raw sum of durations = 3 + 4 + 4 + 4 + 4 + 3 + 4 = 26 days.
# With 6 transitions (sharing one day each), the overall trip length = 26 - 6 = 20 days.

cities = ["Mykonos", "Manchester", "Dubrovnik", "Vienna", "Lisbon", "Riga", "Dublin"]
durations = [3, 4, 4, 4, 4, 3, 4]

# Allowed direct flights (all bidirectional unless noted otherwise):
# 1. Lisbon and Manchester        => (Lisbon, Manchester)           => (4,1)
# 2. Manchester and Dublin         => (Manchester, Dublin)           => (1,6)
# 3. Vienna and Dubrovnik          => (Vienna, Dubrovnik)            => (3,2)
# 4. Riga and Manchester           => (Riga, Manchester)             => (5,1)
# 5. Lisbon and Dublin             => (Lisbon, Dublin)               => (4,6)
# 6. Riga and Dublin               => (Riga, Dublin)                 => (5,6)
# 7. Dubrovnik and Dublin          => (Dubrovnik, Dublin)            => (2,6)
# 8. Lisbon and Riga               => (Lisbon, Riga)                 => (4,5)
# 9. Vienna and Manchester         => (Vienna, Manchester)           => (3,1)
# 10. Vienna and Lisbon            => (Vienna, Lisbon)               => (3,4)
# 11. Manchester and Dubrovnik     => (Manchester, Dubrovnik)        => (1,2)
# 12. Mykonos and Vienna           => (Mykonos, Vienna)              => (0,3)
# 13. Vienna and Dublin            => (Vienna, Dublin)               => (3,6)
# 14. Vienna and Riga              => (Vienna, Riga)                 => (3,5)

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Lisbon <-> Manchester
bidir(4, 1)
# 2. Manchester <-> Dublin
bidir(1, 6)
# 3. Vienna <-> Dubrovnik
bidir(3, 2)
# 4. Riga <-> Manchester
bidir(5, 1)
# 5. Lisbon <-> Dublin
bidir(4, 6)
# 6. Riga <-> Dublin
bidir(5, 6)
# 7. Dubrovnik <-> Dublin
bidir(2, 6)
# 8. Lisbon <-> Riga
bidir(4, 5)
# 9. Vienna <-> Manchester
bidir(3, 1)
# 10. Vienna <-> Lisbon
bidir(3, 4)
# 11. Manchester <-> Dubrovnik
bidir(1, 2)
# 12. Mykonos <-> Vienna
bidir(0, 3)
# 13. Vienna <-> Dublin
bidir(3, 6)
# 14. Vienna <-> Riga
bidir(3, 5)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the permutation for the visitation order, order[i] ∈ {0,...,6}.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if city c is visited then:
# departure[i] = arrivals[i] + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share a transit day: arrival[i+1] = departure[i].
for i in range(n - 1):
    s.add(arrivals[i + 1] == departures[i])

# The overall trip must finish on day 20.
s.add(departures[n - 1] == 20)

# Event-specific constraints:
# Lisbon (city index 4) - friend meeting between day 6 and day 9 ⇒ force arrival = 6.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 6, True))
# Dublin (city index 6) - visit relatives between day 17 and day 20 ⇒ force arrival = 17.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 17, True))

# Connectivity constraints:
# For each consecutive pair (order[i], order[i+1]), there must be a direct flight.
for i in range(n - 1):
    possible_connections = []
    for (frm, to) in allowed_flights:
        possible_connections.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*possible_connections))

# Solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_idx]:10s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")