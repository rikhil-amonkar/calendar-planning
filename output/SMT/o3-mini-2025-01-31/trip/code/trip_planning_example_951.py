from z3 import *

# We define 7 cities with their respective durations and event-related constraints:
# 0: Bucharest  (4 days) – Meet your friends in Bucharest between day 7 and 10, so we force arrival = 7.
# 1: London     (2 days)
# 2: Amsterdam  (2 days) – Attend a wedding in Amsterdam between day 5 and 6, so force arrival = 5.
# 3: Manchester (3 days) – Meet a friend in Manchester between day 10 and 12, so force arrival = 10.
# 4: Dubrovnik  (2 days)
# 5: Reykjavik  (3 days)
# 6: Brussels   (3 days)
#
# Total raw days = 4 + 2 + 2 + 3 + 2 + 3 + 3 = 19 days.
# With 6 transitions (each pair of consecutive visits shares one day),
# the overall trip length is 19 - 6 = 13 days.
cities = ["Bucharest", "London", "Amsterdam", "Manchester", "Dubrovnik", "Reykjavik", "Brussels"]
durations = [4, 2, 2, 3, 2, 3, 3]

# Allowed direct flights (bidirectional):
# 1. Brussels and London         → (Brussels, London)
# 2. Brussels and Manchester     → (Brussels, Manchester)
# 3. Reykjavik and Amsterdam      → (Reykjavik, Amsterdam)
# 4. Brussels and Reykjavik      → (Brussels, Reykjavik)
# 5. Amsterdam and London         → (Amsterdam, London)
# 6. Amsterdam and Manchester     → (Amsterdam, Manchester)
# 7. Manchester and Dubrovnik     → (Manchester, Dubrovnik)
# 8. Reykjavik and London         → (Reykjavik, London)
# 9. London and Manchester        → (London, Manchester)
# 10. London and Bucharest        → (London, Bucharest)
# 11. Bucharest and Manchester    → (Bucharest, Manchester)
# 12. Amsterdam and Bucharest     → (Amsterdam, Bucharest)
# 13. Amsterdam and Dubrovnik     → (Amsterdam, Dubrovnik)
# 14. Brussels and Bucharest      → (Brussels, Bucharest)

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# Helper: Map city names to indices:
# Bucharest: 0, London: 1, Amsterdam: 2, Manchester: 3, Dubrovnik: 4, Reykjavik: 5, Brussels: 6

bidir(6, 1)   # Brussels and London
bidir(6, 3)   # Brussels and Manchester
bidir(5, 2)   # Reykjavik and Amsterdam
bidir(6, 5)   # Brussels and Reykjavik
bidir(2, 1)   # Amsterdam and London
bidir(2, 3)   # Amsterdam and Manchester
bidir(3, 4)   # Manchester and Dubrovnik
bidir(5, 1)   # Reykjavik and London
bidir(1, 3)   # London and Manchester
bidir(1, 0)   # London and Bucharest
bidir(0, 3)   # Bucharest and Manchester
bidir(2, 0)   # Amsterdam and Bucharest
bidir(2, 4)   # Amsterdam and Dubrovnik
bidir(6, 0)   # Brussels and Bucharest

# Set up Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define the visitation order as a permutation of the indices [0,...,6].
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit in the order.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot, the departure day equals arrival + (duration - 1).
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits have overlapping day: arrival of visit i+1 equals departure of visit i.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# The overall trip must finish on day 13.
s.add(departures[n-1] == 13)

# Event-related time constraints:
# Bucharest (city 0): meet your friends between day 7 and 10, so force arrival = 7.
for i in range(n):
    s.add(If(order[i] == 0, arrivals[i] == 7, True))
# Amsterdam (city 2): wedding between day 5 and 6, so force arrival = 5.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 5, True))
# Manchester (city 3): meet a friend between day 10 and 12, so force arrival = 10.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 10, True))

# Connectivity constraints:
# For every pair of consecutive cities in the itinerary, there must be an allowed direct flight from the earlier to the later city.
for i in range(n - 1):
    flight_options = []
    for (frm, to) in allowed_flights:
        flight_options.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*flight_options))

# Solve the model and print the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_index = m.evaluate(order[i]).as_long()
        a_day = m.evaluate(arrivals[i]).as_long()
        d_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_index]:11s}: [{a_day}, {d_day}]")
else:
    print("No solution found")