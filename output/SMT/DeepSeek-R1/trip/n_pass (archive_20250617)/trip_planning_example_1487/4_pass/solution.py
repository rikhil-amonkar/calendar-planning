from z3 import *

# Define city names and their indices
cities = ["Copenhagen", "Geneva", "Mykonos", "Naples", "Prague", "Dubrovnik", "Athens", "Santorini", "Brussels", "Munich"]
n_cities = len(cities)

# Required days per city
days_req = [5, 3, 2, 4, 2, 3, 4, 5, 4, 5]

# Build the set of allowed transitions (direct flights and same city)
allowed_set = set()
for i in range(n_cities):
    allowed_set.add((i, i))

flight_list = [
    "Copenhagen and Dubrovnik", "Brussels and Copenhagen", "Prague and Geneva", "Athens and Geneva",
    "Naples and Dubrovnik", "Athens and Dubrovnik", "Geneva and Mykonos", "Naples and Mykonos",
    "Naples and Copenhagen", "Munich and Mykonos", "Naples and Athens", "Prague and Athens",
    "Santorini and Geneva", "Athens and Santorini", "Naples and Munich", "Prague and Copenhagen",
    "Brussels and Naples", "Athens and Mykonos", "Athens and Copenhagen", "Naples and Geneva",
    "Dubrovnik and Munich", "Brussels and Munich", "Prague and Brussels", "Brussels and Athens",
    "Athens and Munich", "Geneva and Munich", "Copenhagen and Munich", "Brussels and Geneva",
    "Copenhagen and Geneva", "Prague and Munich", "Copenhagen and Santorini", "Naples and Santorini",
    "Geneva and Dubrovnik"
]

for flight in flight_list:
    parts = flight.split(" and ")
    city1 = parts[0]
    city2 = parts[1]
    idx1 = cities.index(city1)
    idx2 = cities.index(city2)
    allowed_set.add((idx1, idx2))
    allowed_set.add((idx2, idx1))

s = Solver()

b = [Int('b_%d' % i) for i in range(28)]

for i in range(28):
    s.add(b[i] >= 0, b[i] < n_cities)

flight_segments = [Bool('flight_%d' % i) for i in range(27)]
for i in range(27):
    s.add(flight_segments[i] == (b[i] != b[i+1]))

s.add(Sum([If(flight_segments[i], 1, 0) for i in range(27)]) == 9)

for city_idx in range(n_cities):
    count_b = Sum([If(b[i] == city_idx, 1, 0) for i in range(28)])
    count_arrival = Sum([If(And(flight_segments[i], b[i+1] == city_idx), 1, 0) for i in range(27)])
    total_days = count_b + count_arrival
    s.add(total_days == days_req[city_idx])

copenhagen_days = []
for i in range(10, 15):
    cond = Or(b[i] == 0, And(i < 27, flight_segments[i], b[i+1] == 0))
    copenhagen_days.append(cond)
s.add(Or(copenhagen_days))

naples_days = []
for i in range(4, 8):
    cond = Or(b[i] == 3, And(i < 27, flight_segments[i], b[i+1] == 3))
    naples_days.append(cond)
s.add(Or(naples_days))

athens_days = []
for i in range(7, 11):
    cond = Or(b[i] == 6, And(i < 27, flight_segments[i], b[i+1] == 6))
    athens_days.append(cond)
s.add(Or(athens_days))

s.add(b[27] == 2)

for i in range(27):
    s.add(Or(Not(flight_segments[i]), (b[i], b[i+1]) in allowed_set))

if s.check() == sat:
    model = s.model()
    res = [model.evaluate(b[i]).as_long() for i in range(28)]
    for day in range(28):
        city_idx = res[day]
        print(f"Day {day+1}: {cities[city_idx]}")
else:
    print("No solution found")