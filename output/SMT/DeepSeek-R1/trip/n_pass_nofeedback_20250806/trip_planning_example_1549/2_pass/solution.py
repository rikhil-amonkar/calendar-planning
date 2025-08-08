from z3 import *
import json

city_list = ["Prague", "Tallinn", "Warsaw", "Porto", "Naples", "Milan", "Lisbon", "Santorini", "Riga", "Stockholm"]
required_days = [5, 3, 2, 3, 5, 3, 5, 5, 4, 2]

bidirectional_edges = [
    ("Riga", "Prague"),
    ("Stockholm", "Milan"),
    ("Riga", "Milan"),
    ("Lisbon", "Stockholm"),
    ("Naples", "Warsaw"),
    ("Lisbon", "Warsaw"),
    ("Naples", "Milan"),
    ("Lisbon", "Naples"),
    ("Tallinn", "Prague"),
    ("Stockholm", "Warsaw"),
    ("Riga", "Warsaw"),
    ("Lisbon", "Riga"),
    ("Riga", "Stockholm"),
    ("Lisbon", "Porto"),
    ("Lisbon", "Prague"),
    ("Milan", "Porto"),
    ("Prague", "Milan"),
    ("Lisbon", "Milan"),
    ("Warsaw", "Porto"),
    ("Warsaw", "Tallinn"),
    ("Santorini", "Milan"),
    ("Stockholm", "Prague"),
    ("Stockholm", "Tallinn"),
    ("Warsaw", "Milan"),
    ("Santorini", "Naples"),
    ("Warsaw", "Prague")
]

directed_edges = [
    ("Stockholm", "Santorini"),
    ("Riga", "Tallinn")
]

edges_set = set()
for a, b in bidirectional_edges:
    a_idx = city_list.index(a)
    b_idx = city_list.index(b)
    edges_set.add((a_idx, b_idx))
    edges_set.add((b_idx, a_idx))
for a, b in directed_edges:
    a_idx = city_list.index(a)
    b_idx = city_list.index(b)
    edges_set.add((a_idx, b_idx))
allowed_pairs = list(edges_set)

s = Solver()

c = [Int('c_%d' % i) for i in range(28)]

for i in range(28):
    s.add(And(c[i] >= 0, c[i] < 10))

flight_days = []
for i in range(27):
    flight_days.append(c[i] != c[i+1])
s.add(Sum([If(cond, 1, 0) for cond in flight_days]) == 9)

for i in range(10):
    total_days = Sum([If(c[d] == i, 1, 0) for d in range(28)])
    s.add(total_days == required_days[i])

for i in range(27):
    from_city = c[i]
    to_city = c[i+1]
    valid_flight = Or([And(from_city == pair[0], to_city == pair[1]) for pair in allowed_pairs])
    s.add(Implies(from_city != to_city, valid_flight))

s.add(c[4] == city_list.index("Riga"))
s.add(c[5] == city_list.index("Riga"))
s.add(c[6] == city_list.index("Riga"))
s.add(c[7] == city_list.index("Riga"))

s.add(Or(c[17] == city_list.index("Tallinn"), c[18] == city_list.index("Tallinn"), c[19] == city_list.index("Tallinn")))

s.add(Or(c[23] == city_list.index("Milan"), c[24] == city_list.index("Milan"), c[25] == city_list.index("Milan")))

if s.check() == sat:
    m = s.model()
    c_vals = [m.evaluate(c[i]).as_long() for i in range(28)]
    
    itinerary_list = []
    for day in range(1, 29):
        city_idx = c_vals[day-1]
        city_name = city_list[city_idx]
        itinerary_list.append({"day": day, "place": city_name})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")