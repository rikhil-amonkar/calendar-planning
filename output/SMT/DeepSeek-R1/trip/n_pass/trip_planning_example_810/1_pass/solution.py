from z3 import *
import json

# Define the cities and their required days
city_names = ["Berlin", "Barcelona", "Lyon", "Nice", "Stockholm", "Athens", "Vilnius"]
req_days = [3, 2, 2, 5, 5, 5, 4]

# Direct flights: list of (city1, city2) by name, convert to indices
flight_pairs = [
    ("Lyon", "Nice"),
    ("Stockholm", "Athens"),
    ("Nice", "Athens"),
    ("Berlin", "Athens"),
    ("Berlin", "Nice"),
    ("Berlin", "Barcelona"),
    ("Berlin", "Vilnius"),
    ("Barcelona", "Nice"),
    ("Athens", "Vilnius"),
    ("Berlin", "Stockholm"),
    ("Nice", "Stockholm"),
    ("Barcelona", "Athens"),
    ("Barcelona", "Stockholm"),
    ("Barcelona", "Lyon")
]

# Create a set of flight connections by indices
flight_set = set()
for c1, c2 in flight_pairs:
    i1 = city_names.index(c1)
    i2 = city_names.index(c2)
    flight_set.add((i1, i2))
    flight_set.add((i2, i1))

# We have 7 stays
n = 7

# Create solver
solver = Solver()

# Sequence of cities (indices) for the 7 stays
seq = [Int(f'seq_{i}') for i in range(n)]

# Start and end days for each stay
s = [Int(f's_{i}') for i in range(n)]
e = [Int(f'e_{i}') for i in range(n)]

# Constraints:

# 1. The sequence is a permutation of 0..6
solver.add(Distinct(seq))

# 2. Each seq[i] is between 0 and 6
for i in range(n):
    solver.add(seq[i] >= 0, seq[i] < n)

# 3. First stay starts on day 1, last stay ends on day 20
solver.add(s[0] == 1)
solver.add(e[n-1] == 20)

# 4. Consecutive stays: the end day of stay i is the start day of stay i+1
for i in range(n-1):
    solver.add(e[i] == s[i+1])

# 5. For each stay, the length = end - start + 1 = required_days[city]
for i in range(n):
    city_index = seq[i]
    for idx in range(n):
        solver.add(If(city_index == idx, e[i] - s[i] + 1 == req_days[idx], True))

# 6. Event constraints:
solver.add(seq[0] == 0)  # Start in Berlin
solver.add(s[0] <= 3, e[0] >= 3)  # Berlin must cover day 3
solver.add(seq[1] == 1)  # Next is Barcelona
solver.add(seq[2] == 2)  # Next is Lyon

# 7. Flight constraints between consecutive stays
for i in range(n-1):
    c1 = seq[i]
    c2 = seq[i+1]
    solver.add(Or([And(c1 == a, c2 == b) for (a, b) in flight_set]))

if solver.check() == sat:
    model = solver.model()
    seq_val = [model.evaluate(seq[i]).as_long() for i in range(n)]
    s_val = [model.evaluate(s[i]).as_long() for i in range(n)]
    e_val = [model.evaluate(e[i]).as_long() for i in range(n)]
    
    itinerary = []

    for i in range(n):
        city = city_names[seq_val[i]]
        start = s_val[i]
        end = e_val[i]
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
        if i < n-1:
            next_city = city_names[seq_val[i+1]]
            itinerary.append({"day_range": f"Day {end}", "place": city})
            itinerary.append({"day_range": f"Day {end}", "place": next_city})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')