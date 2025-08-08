from z3 import *
import json

city_list = ["Prague", "Tallinn", "Warsaw", "Porto", "Naples", "Milan", "Lisbon", "Santorini", "Riga", "Stockholm"]
required_days = [5, 3, 2, 3, 5, 3, 5, 5, 4, 2]

bidirectional_edges = [
    ("Riga", "Prague"), ("Stockholm", "Milan"), ("Riga", "Milan"),
    ("Lisbon", "Stockholm"), ("Naples", "Warsaw"), ("Lisbon", "Warsaw"),
    ("Naples", "Milan"), ("Lisbon", "Naples"), ("Tallinn", "Prague"),
    ("Stockholm", "Warsaw"), ("Riga", "Warsaw"), ("Lisbon", "Riga"),
    ("Riga", "Stockholm"), ("Lisbon", "Porto"), ("Lisbon", "Prague"),
    ("Milan", "Porto"), ("Prague", "Milan"), ("Lisbon", "Milan"),
    ("Warsaw", "Porto"), ("Warsaw", "Tallinn"), ("Santorini", "Milan"),
    ("Stockholm", "Prague"), ("Stockholm", "Tallinn"), ("Warsaw", "Milan"),
    ("Santorini", "Naples"), ("Warsaw", "Prague")
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

itinerary = [Int(f'day_{d}') for d in range(1, 29)]

for day in range(1, 29):
    s.add(itinerary[day-1] >= 0, itinerary[day-1] < 10)

start_day = [Int(f'start_{city}') for city in city_list]
end_day = [Int(f'end_{city}') for city in city_list]

for i in range(10):
    s.add(start_day[i] >= 1, start_day[i] <= 28)
    s.add(end_day[i] >= 1, end_day[i] <= 28)
    s.add(end_day[i] == start_day[i] + required_days[i] - 1)

for i in range(10):
    for j in range(i+1, 10):
        s.add(Or(
            end_day[i] < start_day[j],
            end_day[j] < start_day[i]
        ))

for d in range(1, 29):
    in_city = []
    for i in range(10):
        in_city.append(And(start_day[i] <= d, d <= end_day[i]))
    s.add(Or(in_city))

for d in range(1, 28):
    current_city = itinerary[d-1]
    next_city = itinerary[d]
    s.add(Implies(current_city != next_city, 
                  Or(*[(current_city == a) & (next_city == b) for (a, b) in allowed_pairs])))

riga_idx = city_list.index("Riga")
tallinn_idx = city_list.index("Tallinn")
milan_idx = city_list.index("Milan")

s.add(start_day[riga_idx] == 5)
s.add(start_day[tallinn_idx] <= 20)
s.add(end_day[tallinn_idx] >= 18)
s.add(start_day[milan_idx] <= 26)
s.add(end_day[milan_idx] >= 24)

if s.check() == sat:
    model = s.model()
    itinerary_result = []
    for day in range(1, 29):
        city_index = model.evaluate(itinerary[day-1]).as_long()
        itinerary_result.append({"day": day, "place": city_list[city_index]})
    print(json.dumps({"itinerary": itinerary_result}, indent=2))
else:
    print("No solution found")