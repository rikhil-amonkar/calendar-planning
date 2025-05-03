from z3 import *

# Cities with indices, durations and event constraints:
# 0: Vilnius   (4 days)
# 1: Riga      (3 days)
# 2: Helsinki  (5 days) – Conference in Helsinki between day 17 and day 21 → force arrival = 17.
# 3: Seville   (2 days) – Workshop in Seville between day 8 and day 9 → force arrival = 8.
# 4: Edinburgh (5 days) – Wedding in Edinburgh between day 4 and day 8 → force arrival = 4.
# 5: Barcelona (4 days)
# 6: Munich    (4 days)
#
# The raw durations add up to: 4+3+5+2+5+4+4 = 27.
# With 6 overlaps (transitions) the overall trip length is 27 - 6 = 21 days.

cities = ["Vilnius", "Riga", "Helsinki", "Seville", "Edinburgh", "Barcelona", "Munich"]
durations = [4, 3, 5, 2, 5, 4, 4]

# Allowed direct flights (with one-way flights noted)
# 1. from Riga to Munich            -> one-way: (Riga, Munich)              => (1,6)
# 2. Munich and Seville              -> bidir:   (Munich, Seville)           => (6,3)
# 3. Edinburgh and Seville           -> bidir:   (Edinburgh, Seville)        => (4,3)
# 4. Edinburgh and Barcelona         -> bidir:   (Edinburgh, Barcelona)      => (4,5)
# 5. from Vilnius to Munich           -> one-way: (Vilnius, Munich)             => (0,6)
# 6. Munich and Helsinki             -> bidir:   (Munich, Helsinki)          => (6,2)
# 7. Vilnius and Helsinki            -> bidir:   (Vilnius, Helsinki)         => (0,2)
# 8. Barcelona and Helsinki          -> bidir:   (Barcelona, Helsinki)       => (5,2)
# 9. Riga and Helsinki               -> bidir:   (Riga, Helsinki)            => (1,2)
# 10. Edinburgh and Riga             -> bidir:   (Edinburgh, Riga)           => (4,1)
# 11. Munich and Barcelona           -> bidir:   (Munich, Barcelona)         => (6,5)
# 12. Edinburgh and Helsinki         -> bidir:   (Edinburgh, Helsinki)       => (4,2)
# 13. from Riga to Vilnius            -> one-way: (Riga, Vilnius)             => (1,0)
# 14. Munich and Edinburgh           -> bidir:   (Munich, Edinburgh)         => (6,4)
# 15. Barcelona and Riga             -> bidir:   (Barcelona, Riga)           => (5,1)
# 16. Seville and Barcelona          -> bidir:   (Seville, Barcelona)        => (3,5)

allowed_flights = []

def bidir(a, b):
    allowed_flights.append((a, b))
    allowed_flights.append((b, a))

# 1. One-way: Riga -> Munich
allowed_flights.append((1, 6))
# 2. Munich <-> Seville
bidir(6, 3)
# 3. Edinburgh <-> Seville
bidir(4, 3)
# 4. Edinburgh <-> Barcelona
bidir(4, 5)
# 5. One-way: Vilnius -> Munich
allowed_flights.append((0, 6))
# 6. Munich <-> Helsinki
bidir(6, 2)
# 7. Vilnius <-> Helsinki
bidir(0, 2)
# 8. Barcelona <-> Helsinki
bidir(5, 2)
# 9. Riga <-> Helsinki
bidir(1, 2)
# 10. Edinburgh <-> Riga
bidir(4, 1)
# 11. Munich <-> Barcelona
bidir(6, 5)
# 12. Edinburgh <-> Helsinki
bidir(4, 2)
# 13. One-way: Riga -> Vilnius
allowed_flights.append((1, 0))
# 14. Munich <-> Edinburgh
bidir(6, 4)
# 15. Barcelona <-> Riga
bidir(5, 1)
# 16. Seville <-> Barcelona
bidir(3, 5)

# Set up the Z3 solver.
s = Solver()
n = len(cities)  # 7 cities

# Define permutation variables for the order of visits.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visited city.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot, departure day = arrival day + (duration - 1)
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share a transit day.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 21.
s.add(departures[n-1] == 21)

# Event-specific constraints:
# Helsinki (city index 2): Conference between day 17 and 21 → force arrival = 17.
for i in range(n):
    s.add(If(order[i] == 2, arrivals[i] == 17, True))
# Seville (city index 3): Workshop between day 8 and 9 → force arrival = 8.
for i in range(n):
    s.add(If(order[i] == 3, arrivals[i] == 8, True))
# Edinburgh (city index 4): Wedding between day 4 and 8 → force arrival = 4.
for i in range(n):
    s.add(If(order[i] == 4, arrivals[i] == 4, True))

# Connectivity constraints:
# Each consecutive pair of cities in the itinerary must be connected by a direct flight.
for i in range(n - 1):
    allowed_connection = []
    for (frm, to) in allowed_flights:
        allowed_connection.append(And(order[i] == frm, order[i+1] == to))
    s.add(Or(*allowed_connection))

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