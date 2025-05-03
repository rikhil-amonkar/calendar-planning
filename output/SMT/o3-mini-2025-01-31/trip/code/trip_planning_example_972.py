from z3 import *

# Cities (indices) with durations and event constraints:
# 0: Valencia  (4 days)
# 1: Geneva    (4 days)
# 2: Milan     (4 days) – Meet friends in Milan between day 1 and day 4 → force arrival = 1.
# 3: Venice    (2 days)
# 4: Helsinki  (2 days) – Annual show in Helsinki from day 5 to day 6 → force arrival = 5.
# 5: Madrid    (2 days)
# 6: Nice      (3 days)
#
# Total raw days = 4 + 4 + 4 + 2 + 2 + 2 + 3 = 21.
# There are 6 transitions (overlapping days) so overall trip length = 21 - 6 = 15 days.

cities = ["Valencia", "Geneva", "Milan", "Venice", "Helsinki", "Madrid", "Nice"]
durations = [4, 4, 4, 2, 2, 2, 3]

# Allowed direct flights (bidirectional):
# 1. Helsinki and Nice         -> (Helsinki, Nice)    => (4, 6)
# 2. Madrid and Nice           -> (Madrid, Nice)      => (5, 6)
# 3. Helsinki and Geneva       -> (Helsinki, Geneva)  => (4, 1)
# 4. Milan and Valencia        -> (Milan, Valencia)   => (2, 0)
# 5. Milan and Helsinki        -> (Milan, Helsinki)   => (2, 4)
# 6. Madrid and Valencia       -> (Madrid, Valencia)  => (5, 0)
# 7. Madrid and Venice         -> (Madrid, Venice)    => (5, 3)
# 8. Helsinki and Venice       -> (Helsinki, Venice)  => (4, 3)
# 9. Milan and Madrid          -> (Milan, Madrid)     => (2, 5)
# 10. Madrid and Geneva        -> (Madrid, Geneva)    => (5, 1)
# 11. Nice and Geneva          -> (Nice, Geneva)      => (6, 1)
# 12. Geneva and Valencia      -> (Geneva, Valencia)  => (1, 0)
# 13. Venice and Nice          -> (Venice, Nice)      => (3, 6)
# 14. Madrid and Helsinki      -> (Madrid, Helsinki)  => (5, 4)

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))
    
bidir(4, 6)  # Helsinki <-> Nice
bidir(5, 6)  # Madrid <-> Nice
bidir(4, 1)  # Helsinki <-> Geneva
bidir(2, 0)  # Milan <-> Valencia
bidir(2, 4)  # Milan <-> Helsinki
bidir(5, 0)  # Madrid <-> Valencia
bidir(5, 3)  # Madrid <-> Venice
bidir(4, 3)  # Helsinki <-> Venice
bidir(2, 5)  # Milan <-> Madrid
bidir(5, 1)  # Madrid <-> Geneva
bidir(6, 1)  # Nice <-> Geneva
bidir(1, 0)  # Geneva <-> Valencia
bidir(3, 6)  # Venice <-> Nice
bidir(5, 4)  # Madrid <-> Helsinki

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Permutation: order[i] gives the city visited in the ith slot.
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
# departure[i] = arrivals[i] + (durations[c] - 1)
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share one transit day:
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 15.
s.add(departures[n-1] == 15)

# Event-specific constraints:
# Milan (city index 2): meet friends between day 1 and day 4 → force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 1, True))
# Helsinki (city index 4): annual show from day 5 to day 6 → force arrival = 5.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 5, True))

# Connectivity constraints: each consecutive pair must have a direct flight.
for i in range(n-1):
    possible_flights = []
    for (frm, to) in allowed_flights:
        possible_flights.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*possible_flights))

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