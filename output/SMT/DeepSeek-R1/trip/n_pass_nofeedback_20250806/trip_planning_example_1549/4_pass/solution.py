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

s = Solver()

seq = [Int(f'seq_{i}') for i in range(10)]
start_day = [Int(f'start_{city}') for city in city_list]

for i in range(10):
    s.add(seq[i] >= 0, seq[i] < 10)
s.add(Distinct(seq))

for i in range(10):
    s.add(start_day[i] >= 1)
    s.add(start_day[i] <= 28 - required_days[i] + 1)

s.add(start_day[seq[0]] == 1)
s.add(start_day[seq[9]] + required_days[seq[9]] == 29)

for i in range(9):
    curr_city = seq[i]
    next_city = seq[i+1]
    s.add(start_day[next_city] == start_day[curr_city] + required_days[curr_city])

for i in range(9):
    curr_city = seq[i]
    next_city = seq[i+1]
    s.add(Or(*[(curr_city == a) & (next_city == b) for (a, b) in allowed_pairs]))

riga_idx = city_list.index("Riga")
tallinn_idx = city_list.index("Tallinn")
milan_idx = city_list.index("Milan")

s.add(start_day[riga_idx] <= 5)
s.add(start_day[riga_idx] + required_days[riga_idx] - 1 >= 8)

s.add(Or(
    start_day[tallinn_idx] <= 18,
    start_day[tallinn_idx] <= 19,
    start_day[tallinn_idx] <= 20
))
s.add(Or(
    start_day[tallinn_idx] + required_days[tallinn_idx] - 1 >= 18,
    start_day[tallinn_idx] + required_days[tallinn_idx] - 1 >= 19,
    start_day[tallinn_idx] + required_days[tallinn_idx] - 1 >= 20
))

s.add(Or(
    start_day[milan_idx] <= 24,
    start_day[milan_idx] <= 25,
    start_day[milan_idx] <= 26
))
s.add(Or(
    start_day[milan_idx] + required_days[milan_idx] - 1 >= 24,
    start_day[milan_idx] + required_days[milan_idx] - 1 >= 25,
    start_day[milan_idx] + required_days[milan_idx] - 1 >= 26
))

if s.check() == sat:
    model = s.model()
    seq_vals = [model.evaluate(seq[i]).as_long() for i in range(10)]
    start_vals = [model.evaluate(start_day[i]).as_long() for i in range(10)]
    
    itinerary = []
    for day in range(1, 29):
        for i in range(10):
            start = start_vals[i]
            end = start + required_days[i] - 1
            if start <= day <= end:
                itinerary.append({"day": day, "place": city_list[i]})
                break
        else:
            itinerary.append({"day": day, "place": "In transit"})
    
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found")