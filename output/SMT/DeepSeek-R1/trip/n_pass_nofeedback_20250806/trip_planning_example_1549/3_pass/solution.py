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

allowed_pairs = set()
for a, b in bidirectional_edges:
    a_idx = city_list.index(a)
    b_idx = city_list.index(b)
    allowed_pairs.add((a_idx, b_idx))
    allowed_pairs.add((b_idx, a_idx))
for a, b in directed_edges:
    a_idx = city_list.index(a)
    b_idx = city_list.index(b)
    allowed_pairs.add((a_idx, b_idx))
allowed_pairs = list(allowed_pairs)

s = Solver()

seq = [Int('seq_%d' % i) for i in range(10)]
start_day = [Int('start_%s' % city) for city in city_list]

for i in range(10):
    s.add(seq[i] >= 0, seq[i] < 10)
s.add(Distinct(seq))

for i in range(10):
    s.add(start_day[i] >= 1)
    s.add(start_day[i] <= 28 - required_days[i] + 1)

for i in range(10):
    s.add(Implies(seq[0] == i, start_day[i] == 1))

for i in range(10):
    s.add(Implies(seq[9] == i, start_day[i] + required_days[i] == 29))

for k in range(9):
    for i in range(10):
        for j in range(10):
            s.add(Implies(And(seq[k] == i, seq[k+1] == j), 
                          start_day[j] == start_day[i] + required_days[i]))

for k in range(9):
    disj = []
    for (a, b) in allowed_pairs:
        disj.append(And(seq[k] == a, seq[k+1] == b))
    s.add(Or(disj))

riga_idx = city_list.index("Riga")
tallinn_idx = city_list.index("Tallinn")
milan_idx = city_list.index("Milan")

s.add(start_day[riga_idx] == 5)
s.add(start_day[tallinn_idx] <= 20)
s.add(start_day[tallinn_idx] + required_days[tallinn_idx] - 1 >= 18)
s.add(start_day[milan_idx] <= 26)
s.add(start_day[milan_idx] + required_days[milan_idx] - 1 >= 24)

if s.check() == sat:
    m = s.model()
    start_vals = [m.evaluate(start_day[i]).as_long() for i in range(10)]
    seq_vals = [m.evaluate(seq[i]).as_long() for i in range(10)]
    
    day_to_city = {}
    for city_idx in range(10):
        start = start_vals[city_idx]
        end = start + required_days[city_idx] - 1
        for day in range(start, end + 1):
            day_to_city[day] = city_list[city_idx]
    
    itinerary_list = []
    for day in range(1, 29):
        city_name = day_to_city[day]
        itinerary_list.append({"day": day, "place": city_name})
    
    print(json.dumps({"itinerary": itinerary_list}, indent=2))
else:
    print("No solution found")