from z3 import *

# Cities with indices, durations, and event constraints:
# 0: Valencia   (3 days)
# 1: Salzburg   (5 days)
# 2: Amsterdam  (5 days) – Visit relatives in Amsterdam between day 7 and day 11 ⇒ force arrival = 7.
# 3: Zurich     (2 days)
# 4: Istanbul   (3 days)
# 5: Geneva     (3 days) – Wedding in Geneva between day 15 and day 17 ⇒ force arrival = 15.
# 6: Riga       (2 days)
#
# Total raw days = 3 + 5 + 5 + 2 + 3 + 3 + 2 = 23.
# With 6 transitions (overlap of one day per transition),
# overall trip length = 23 - 6 = 17 days.
cities = ["Valencia", "Salzburg", "Amsterdam", "Zurich", "Istanbul", "Geneva", "Riga"]
durations = [3, 5, 5, 2, 3, 3, 2]

# Allowed direct flights (all bidirectional):
# 1. Istanbul and Valencia    -> (Istanbul, Valencia): (4, 0)
# 2. Amsterdam and Valencia   -> (Amsterdam, Valencia): (2, 0)
# 3. Amsterdam and Geneva     -> (Amsterdam, Geneva): (2, 5)
# 4. Salzburg and Istanbul    -> (Salzburg, Istanbul): (1, 4)
# 5. Istanbul and Zurich      -> (Istanbul, Zurich): (4, 3)
# 6. Zurich and Valencia      -> (Zurich, Valencia): (3, 0)
# 7. Istanbul and Geneva      -> (Istanbul, Geneva): (4, 5)
# 8. Riga and Zurich          -> (Riga, Zurich): (6, 3)
# 9. Amsterdam and Zurich     -> (Amsterdam, Zurich): (2, 3)
# 10. Istanbul and Amsterdam  -> (Istanbul, Amsterdam): (4, 2)
# 11. Valencia and Geneva       -> (Valencia, Geneva): (0, 5)
# 12. Istanbul and Riga       -> (Istanbul, Riga): (4, 6)
# 13. Amsterdam and Riga      -> (Amsterdam, Riga): (2, 6)
# 14. Zurich and Geneva       -> (Zurich, Geneva): (3, 5)

allowed_flights = []
def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

bidir(4, 0)  # Istanbul <-> Valencia
bidir(2, 0)  # Amsterdam <-> Valencia
bidir(2, 5)  # Amsterdam <-> Geneva
bidir(1, 4)  # Salzburg <-> Istanbul
bidir(4, 3)  # Istanbul <-> Zurich
bidir(3, 0)  # Zurich <-> Valencia
bidir(4, 5)  # Istanbul <-> Geneva
bidir(6, 3)  # Riga <-> Zurich
bidir(2, 3)  # Amsterdam <-> Zurich
bidir(4, 2)  # Istanbul <-> Amsterdam
bidir(0, 5)  # Valencia <-> Geneva
bidir(4, 6)  # Istanbul <-> Riga
bidir(2, 6)  # Amsterdam <-> Riga
bidir(3, 5)  # Zurich <-> Geneva

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define a permutation variable "order" representing the order in which cities are visited.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each city visit in the itinerary.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, compute departure = arrival + (duration - 1)
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share one transit day:
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 17.
s.add(departures[n-1] == 17)

# Event-specific constraints:
# Amsterdam (city index 2): relatives visit between day 7 and day 11, force arrival = 7.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 7, True))
# Geneva (city index 5): wedding between day 15 and day 17, force arrival = 15.
for i in range(n):
    s.add(If(order[i] == 5, arrivals[i] == 15, True))

# Connectivity constraints: each consecutive pair in the itinerary must have a direct flight.
for i in range(n - 1):
    flight_options = []
    for (frm, to) in allowed_flights:
        flight_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*flight_options))

# Solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:10s}: [{a_day}, {d_day}]")
else:
    print("No solution found")