from z3 import *

# We have 7 cities with the following durations and event constraints:
# 0: Tallinn   (4 days)
# 1: Brussels  (4 days)
# 2: Barcelona (4 days) – Meet a friend in Barcelona between day 1 and day 4 ⇒ force arrival = 1.
# 3: Munich    (5 days) – Conference in Munich between day 4 and day 8 ⇒ force arrival = 4.
# 4: Manchester(4 days)
# 5: Zurich    (4 days)
# 6: Split     (3 days) – Meet friends at Split between day 14 and day 16 ⇒ force arrival = 14.
cities = ["Tallinn", "Brussels", "Barcelona", "Munich", "Manchester", "Zurich", "Split"]
durations = [4, 4, 4, 5, 4, 4, 3]

# Total raw days = 4+4+4+5+4+4+3 = 28.
# There are 6 transitions (each consecutive visit shares one day),
# so overall trip duration = 28 - 6 = 22 days.

# Allowed direct flights (bidirectional):
# 1. Barcelona and Brussels     -> {Barcelona, Brussels} -> {2, 1}
# 2. Brussels and Manchester    -> {Brussels, Manchester} -> {1, 4}
# 3. Munich and Tallinn         -> {Munich, Tallinn} -> {3, 0}
# 4. Barcelona and Zurich       -> {Barcelona, Zurich} -> {2, 5}
# 5. Split and Zurich           -> {Split, Zurich} -> {6, 5}
# 6. Manchester and Split       -> {Manchester, Split} -> {4, 6}
# 7. Barcelona and Split        -> {Barcelona, Split} -> {2, 6}
# 8. Barcelona and Munich       -> {Barcelona, Munich} -> {2, 3}
# 9. Munich and Split           -> {Munich, Split} -> {3, 6}
# 10. Barcelona and Manchester  -> {Barcelona, Manchester} -> {2, 4}
# 11. Barcelona and Tallinn     -> {Barcelona, Tallinn} -> {2, 0}
# 12. Brussels and Tallinn      -> {Brussels, Tallinn} -> {1, 0}
# 13. Zurich and Tallinn        -> {Zurich, Tallinn} -> {5, 0}
# 14. Brussels and Zurich       -> {Brussels, Zurich} -> {1, 5}
# 15. Manchester and Zurich     -> {Manchester, Zurich} -> {4, 5}
# 16. Munich and Zurich         -> {Munich, Zurich} -> {3, 5}
# 17. Munich and Manchester     -> {Munich, Manchester} -> {3, 4}
# 18. Munich and Brussels       -> {Munich, Brussels} -> {3, 1}
direct_flights = [
    ("Barcelona", "Brussels"),
    ("Brussels", "Manchester"),
    ("Munich", "Tallinn"),
    ("Barcelona", "Zurich"),
    ("Split", "Zurich"),
    ("Manchester", "Split"),
    ("Barcelona", "Split"),
    ("Barcelona", "Munich"),
    ("Munich", "Split"),
    ("Barcelona", "Manchester"),
    ("Barcelona", "Tallinn"),
    ("Brussels", "Tallinn"),
    ("Zurich", "Tallinn"),
    ("Brussels", "Zurich"),
    ("Manchester", "Zurich"),
    ("Munich", "Zurich"),
    ("Munich", "Manchester"),
    ("Munich", "Brussels")
]

# Map city names to indices.
city_to_idx = {city: idx for idx, city in enumerate(cities)}

# Build allowed unordered flight pairs.
allowed_pairs = set()
for a, b in direct_flights:
    allowed_pairs.add(frozenset({city_to_idx[a], city_to_idx[b]}))

# Set up the Z3 solver.
s = Solver()
n = len(cities)

# Define the visitation order as a permutation of city indices.
order = [Int(f"order_{i}") for i in range(n)]
for i in range(n):
    s.add(And(order[i] >= 0, order[i] < n))
s.add(Distinct(order))

# Define arrival and departure day variables for each visit.
arrivals = [Int(f"arr_{i}") for i in range(n)]
departures = [Int(f"dep_{i}") for i in range(n)]

# The trip starts on day 1.
s.add(arrivals[0] == 1)

# For each visit slot i, if the visited city is c then:
# departure = arrival + durations[c] - 1.
for i in range(n):
    s.add(Or([If(order[i] == c, departures[i] == arrivals[i] + durations[c] - 1, False)
              for c in range(n)]))

# Consecutive visits share the transit day:
# arrival of visit i+1 equals departure of visit i.
for i in range(n - 1):
    s.add(arrivals[i+1] == departures[i])

# Overall trip must finish on day 22.
s.add(departures[n-1] == 22)

# Time-specific event constraints:
# Barcelona (city 2): Meet a friend between day 1 and day 4 ⇒ force arrival = 1.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Barcelona"],
             arrivals[i] == 1,
             True))
# Munich (city 3): Conference between day 4 and day 8 ⇒ force arrival = 4.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Munich"],
             arrivals[i] == 4,
             True))
# Split (city 6): Meet friends between day 14 and day 16 ⇒ force arrival = 14.
for i in range(n):
    s.add(If(order[i] == city_to_idx["Split"],
             arrivals[i] == 14,
             True))

# Connectivity constraints:
# Each consecutive pair in the itinerary must be connected by a direct flight.
for i in range(n - 1):
    valid_flight = []
    for pair in allowed_pairs:
        pair_list = list(pair)
        a, b = pair_list[0], pair_list[1]
        valid_flight.append(And(order[i] == a, order[i+1] == b))
        valid_flight.append(And(order[i] == b, order[i+1] == a))
    s.add(Or(*valid_flight))

# Solve the model and output the itinerary.
if s.check() == sat:
    m = s.model()
    print("Itinerary (City, arrival day, departure day):")
    for i in range(n):
        city_idx = m.evaluate(order[i]).as_long()
        arr_day = m.evaluate(arrivals[i]).as_long()
        dep_day = m.evaluate(departures[i]).as_long()
        print(f"  {cities[city_idx]:12s}: [{arr_day}, {dep_day}]")
else:
    print("No solution found")