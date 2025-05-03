from z3 import *

# Cities and durations with event constraints:
# 0: Madrid   (5 days) – Annual show from day 1 to day 5 → force arrival = 1.
# 1: Brussels (5 days) – Meet friends between day 6 and day 10 → force arrival = 6.
# 2: Mykonos  (5 days)
# 3: Zurich   (2 days)
# 4: Seville  (2 days)
# 5: Hamburg  (2 days)
# 6: Nice     (2 days) – Workshop between day 16 and day 17 → force arrival = 16.
#
# Total raw days = 5+5+5+2+2+2+2 = 23.
# There are 6 transitions (overlap days), so overall trip length = 23 - 6 = 17 days.
cities = ["Madrid", "Brussels", "Mykonos", "Zurich", "Seville", "Hamburg", "Nice"]
durations = [5, 5, 5, 2, 2, 2, 2]

# Allowed direct flights (bidirectional connections)
# 1. Madrid and Brussels
# 2. Madrid and Zurich
# 3. Hamburg and Nice
# 4. Brussels and Hamburg
# 5. Madrid and Hamburg
# 6. Seville and Brussels
# 7. Mykonos and Nice
# 8. Zurich and Nice
# 9. Madrid and Nice
# 10. Madrid and Seville
# 11. Madrid and Mykonos
# 12. Brussels and Nice
# 13. Hamburg and Zurich
# 14. Brussels and Zurich
# 15. Zurich and Mykonos

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Madrid <-> Brussels
bidir(0, 1)
# 2. Madrid <-> Zurich
bidir(0, 3)
# 3. Hamburg <-> Nice
bidir(5, 6)
# 4. Brussels <-> Hamburg
bidir(1, 5)
# 5. Madrid <-> Hamburg
bidir(0, 5)
# 6. Seville <-> Brussels
bidir(4, 1)
# 7. Mykonos <-> Nice
bidir(2, 6)
# 8. Zurich <-> Nice
bidir(3, 6)
# 9. Madrid <-> Nice
bidir(0, 6)
# 10. Madrid <-> Seville
bidir(0, 4)
# 11. Madrid <-> Mykonos
bidir(0, 2)
# 12. Brussels <-> Nice
bidir(1, 6)
# 13. Hamburg <-> Zurich
bidir(5, 3)
# 14. Brussels <-> Zurich
bidir(1, 3)
# 15. Zurich <-> Mykonos
bidir(3, 2)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define permutation variables for the order of visits.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit, departure = arrival + (duration - 1)
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share one transit day.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 17.
s.add(departures[n-1] == 17)

# Event-specific constraints:
# Madrid (city index 0): annual show from day 1 to day 5 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 1, True))
# Brussels (city index 1): meet friends between day 6 and day 10 → force arrival = 6.
for i in range(n):
    s.add(If(order[i] == 1, arrivals[i] == 6, True))
# Nice (city index 6): workshop between day 16 and day 17 → force arrival = 16.
for i in range(n):
    s.add(If(order[i] == 6, arrivals[i] == 16, True))

# Connectivity constraints:
# Each consecutive pair of cities must be connected by a direct flight.
for i in range(n-1):
    flight_options = []
    for (frm, to) in allowed_flights:
        flight_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*flight_options))

# Solve the model and print the itinerary.
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