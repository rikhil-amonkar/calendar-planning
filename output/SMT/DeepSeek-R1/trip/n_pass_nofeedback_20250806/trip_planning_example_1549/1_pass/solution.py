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

flight_d = [c[i] != c[i+1] for i in range(27)]
s.add(Sum([If(cond, 1, 0) for cond in flight_d]) == 9)

in_city = [[None for _ in range(28)] for _ in range(10)]
for i in range(10):
    for d in range(28):
        if d < 27:
            in_city[i][d] = Or(c[d] == i, And(c[d+1] == i, c[d] != c[d+1]))
        else:
            in_city[i][d] = (c[d] == i)

for i in range(10):
    total_days = Sum([If(in_city[i][d], 1, 0) for d in range(28)])
    s.add(total_days == required_days[i])

for d in range(27):
    from_city = c[d]
    to_city = c[d+1]
    flight_valid = Or([And(from_city == pair[0], to_city == pair[1]) for pair in allowed_pairs])
    s.add(Implies(flight_d[d], flight_valid))

s.add(in_city[8][4])
s.add(in_city[8][5])
s.add(in_city[8][6])
s.add(in_city[8][7])

s.add(Or(in_city[1][17], in_city[1][18], in_city[1][19]))
s.add(Or(in_city[5][23], in_city[5][24], in_city[5][25]))

if s.check() == sat:
    m = s.model()
    c_vals = [m.evaluate(c[i]).as_long() for i in range(28)]
    
    itinerary_list = []
    for day in range(1, 29):
        idx = day - 1
        city1_index = c_vals[idx]
        city1_name = city_list[city1_index]
        itinerary_list.append({"day": day, "place": city1_name})
        if day < 28:
            city2_index = c_vals[idx+1]
            if city1_index != city2_index:
                city2_name = city_list[city2_index]
                itinerary_list.append({"day": day, "place": city2_name})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")