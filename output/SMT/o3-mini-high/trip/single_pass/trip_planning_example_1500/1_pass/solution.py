from z3 import *
import json

# There are 10 cities. We assign each a unique index.
# 0: London
# 1: Hamburg
# 2: Reykjavik
# 3: Zurich
# 4: Bucharest
# 5: Barcelona
# 6: Stuttgart
# 7: Stockholm
# 8: Tallinn
# 9: Milan

cities_list = ["London", "Hamburg", "Reykjavik", "Zurich", "Bucharest", "Barcelona",
               "Stuttgart", "Stockholm", "Tallinn", "Milan"]

# Required day counts for each city (the “presence‐count”).
# Note: On a flight day (when you fly from city A to city B) that day will count 1 for A and 1 for B.
required_days = {
    0: 3,   # London (plus the annual show on days 1-3)
    1: 5,   # Hamburg
    2: 5,   # Reykjavik (and must be in Reykjavik on days 9-13 for relatives)
    3: 2,   # Zurich (and must attend conference in Zurich on days 7-8)
    4: 2,   # Bucharest
    5: 4,   # Barcelona
    6: 5,   # Stuttgart
    7: 2,   # Stockholm
    8: 4,   # Tallinn
    9: 5    # Milan (and meet friends there at some point between days 3-7)
}

# There are 28 days in total.
n_days = 28

# Allowed direct flights (treated as undirected edges).
# Each tuple appears in both orders.
allowed_flights = [
    (0, 1), (1, 0),      # London <-> Hamburg
    (0, 2), (2, 0),      # London <-> Reykjavik
    (9, 5), (5, 9),      # Milan <-> Barcelona
    (2, 5), (5, 2),      # Reykjavik <-> Barcelona
    (2, 6), (6, 2),      # Reykjavik <-> Stuttgart
    (7, 2), (2, 7),      # Stockholm <-> Reykjavik
    (0, 6), (6, 0),      # London <-> Stuttgart
    (9, 3), (3, 9),      # Milan <-> Zurich
    (0, 5), (5, 0),      # London <-> Barcelona
    (7, 1), (1, 7),      # Stockholm <-> Hamburg
    (3, 5), (5, 3),      # Zurich <-> Barcelona
    (7, 6), (6, 7),      # Stockholm <-> Stuttgart
    (9, 1), (1, 9),      # Milan <-> Hamburg
    (7, 8), (8, 7),      # Stockholm <-> Tallinn
    (1, 4), (4, 1),      # Hamburg <-> Bucharest
    (0, 4), (4, 0),      # London <-> Bucharest
    (9, 7), (7, 9),      # Milan <-> Stockholm
    (6, 1), (1, 6),      # Stuttgart <-> Hamburg
    (0, 3), (3, 0),      # London <-> Zurich
    (9, 2), (2, 9),      # Milan <-> Reykjavik
    (0, 7), (7, 0),      # London <-> Stockholm
    (9, 6), (6, 9),      # Milan <-> Stuttgart
    (7, 5), (5, 7),      # Stockholm <-> Barcelona
    (0, 9), (9, 0),      # London <-> Milan
    (3, 1), (1, 3),      # Zurich <-> Hamburg
    (4, 5), (5, 4),      # Bucharest <-> Barcelona
    (3, 7), (7, 3),      # Zurich <-> Stockholm
    (5, 8), (8, 5),      # Barcelona <-> Tallinn
    (3, 2), (2, 3),      # Zurich <-> Reykjavik
    (3, 4), (4, 3)       # Zurich <-> Bucharest
]

# Create a Z3 solver instance.
solver = Solver()

# For each day 1..n_days we create:
#   p[i] = the departure city (or the city you are in if no flight that day)
#   q[i] = the arrival city (if you fly, this will be different; if no flight, q[i] == p[i])
#   f[i] = a Boolean flag indicating whether you take a flight on day i.
# (Note that when f[i] is True, day i “counts” once for p[i] and once for q[i].)
p = [Int(f"p_{i}") for i in range(n_days+1)]
q = [Int(f"q_{i}") for i in range(n_days+1)]
f = [Bool(f"f_{i}") for i in range(n_days+1)]

# Domain constraints: both p[i] and q[i] must be valid city indices.
for i in range(1, n_days+1):
    solver.add(p[i] >= 0, p[i] < 10)
    solver.add(q[i] >= 0, q[i] < 10)

# Day 1: No flight (and so p[1] == q[1]).
solver.add(f[1] == False)
solver.add(p[1] == q[1])

# For each day i, if there is no flight then you stay in the same city.
# Otherwise (if f[i] is True) you must change city and the flight must be allowed.
for i in range(1, n_days+1):
    solver.add(If(f[i], p[i] != q[i], p[i] == q[i]))
    solver.add(Implies(f[i], Or([And(p[i] == a, q[i] == b) for (a, b) in allowed_flights])))

# Consistency: The arrival city of day i becomes the departure city of day i+1.
for i in range(1, n_days):
    solver.add(q[i] == p[i+1])
    
# The required total “presence‐count” is 37.
# Each non-flight day contributes 1 to one city,
# and each flight day contributes 1 for the departure and 1 for the arrival.
# Since there are 28 days, the number of flight days must be exactly 9 
# (because 28 + (# flight days) = 37).
solver.add(Sum([If(f[i], 1, 0) for i in range(1, n_days+1)]) == 9)

# Fixed date constraints:
# 1. Attend an annual show in London on days 1-3.
for i in [1, 2, 3]:
    # On a flight day, one of the two cities must be London; otherwise, you must be in London.
    solver.add(If(f[i], Or(p[i] == 0, q[i] == 0), p[i] == 0))

# 2. Conference in Zurich on days 7 and 8.
for i in [7, 8]:
    solver.add(If(f[i], Or(p[i] == 3, q[i] == 3), p[i] == 3))
    
# 3. In Reykjavik (for relatives) on days 9 to 13.
for i in range(9, 14):
    solver.add(If(f[i], Or(p[i] == 2, q[i] == 2), p[i] == 2))
    
# 4. You want to meet your friends in Milan at some point between days 3 and 7.
# That is, on at least one day i in {3,4,5,6,7}, Milan (city 9) must appear.
solver.add(Or([If(f[i], Or(p[i] == 9, q[i] == 9), p[i] == 9) for i in range(3, 8)]))

# Duration constraints for each city.
# For each day i, if f[i] is False then that day contributes 1 to p[i],
# and if f[i] is True then that day contributes 1 to p[i] and 1 to q[i].
for city in range(10):
    day_count = Sum([If(f[i],
                        (If(p[i] == city, 1, 0) + If(q[i] == city, 1, 0)),
                        If(p[i] == city, 1, 0))
                     for i in range(1, n_days+1)])
    solver.add(day_count == required_days[city])

# Solve the model.
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(1, n_days+1):
        # On a non-flight day, you are only in one city.
        # On a flight day, you are in both the departure and arrival cities.
        if is_true(model.evaluate(f[i])):
            day_cities = [cities_list[model.evaluate(p[i]).as_long()],
                          cities_list[model.evaluate(q[i]).as_long()]]
        else:
            day_cities = [cities_list[model.evaluate(p[i]).as_long()]]
        itinerary.append({"day": i, "cities": day_cities})
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=4))
else:
    print("No solution found.")