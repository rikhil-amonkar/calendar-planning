from z3 import *

# Cities and durations:
# 0: Nice       (5 days)
# 1: Split      (2 days)
# 2: Copenhagen (3 days) – Conference from day 1 to day 3, so force arrival = 1.
# 3: Brussels   (5 days)
# 4: London     (2 days)
# 5: Tallinn    (4 days) – Annual show from day 6 to day 9, so force arrival = 6.
# 6: Istanbul   (4 days)
#
# Total raw days = 5+2+3+5+2+4+4 = 25 days.
# There are 6 transitions (each consecutive visit shares one day),
# so overall trip length = 25 - 6 = 19 days.
cities = ["Nice", "Split", "Copenhagen", "Brussels", "London", "Tallinn", "Istanbul"]
durations = [5, 2, 3, 5, 2, 4, 4]

# Allowed direct flights with directions:
# For nearly all flights, the connection is bidirectional.
# Exception: "from Istanbul to Tallinn" is one-way only.
# List of allowed flights (each as a tuple (from, to) using city indices):
allowed_flights = []
def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. Istanbul and Nice:
bidir(6, 0)
# 2. London and Split:
bidir(4, 1)
# 3. Brussels and London:
bidir(3, 4)
# 4. Copenhagen and London:
bidir(2, 4)
# 5. Nice and London:
bidir(0, 4)
# 6. Tallinn and Brussels:
bidir(5, 3)
# 7. Copenhagen and Tallinn:
bidir(2, 5)
# 8. Copenhagen and Split:
bidir(2, 1)
# 9. Copenhagen and Brussels:
bidir(2, 3)
# 10. Copenhagen and Istanbul:
bidir(2, 6)
# 11. from Istanbul to Tallinn: one-way only, so add only this direction.
allowed_flights.append((6, 5))
# 12. Brussels and Nice:
bidir(3, 0)
# 13. Copenhagen and Nice:
bidir(2, 0)
# 14. Istanbul and Brussels:
bidir(6, 3)
# 15. Istanbul and London:
bidir(6, 4)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the visitation order as a permutation of the city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, compute departure based on the city's duration:
# departure = arrival + duration - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share one day: arrival of slot i+1 equals departure of slot i.
for i in range(n-1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 19.
s.add(departures[n-1] == 19)

# Time-specific event constraints:
# Copenhagen (city 2): attend conference during day 1 to 3, force arrival = 1.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 1, True))
# Tallinn (city 5): annual show from day 6 to 9, force arrival = 6.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 6, True))

# Connectivity constraints:
# Each consecutive pair of visits must be connected by an allowed direct flight (respecting direction).
for i in range(n-1):
    conn_options = []
    for (frm, to) in allowed_flights:
        conn_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*conn_options))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:12s}: [{a_day}, {d_day}]")
else:
    print("No solution found")