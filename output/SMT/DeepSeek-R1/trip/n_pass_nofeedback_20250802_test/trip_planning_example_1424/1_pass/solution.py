from z3 import *
import json

cities = ['Warsaw', 'Porto', 'Naples', 'Brussels', 'Split', 'Reykjavik', 'Amsterdam', 'Lyon', 'Helsinki', 'Valencia']

stays = {
    'Warsaw': 3,
    'Porto': 5,
    'Naples': 4,
    'Brussels': 3,
    'Split': 3,
    'Reykjavik': 5,
    'Amsterdam': 4,
    'Lyon': 3,
    'Helsinki': 4,
    'Valencia': 2
}

events = {
    'Porto': (1, 5),
    'Amsterdam': (5, 8),
    'Helsinki': (8, 11),
    'Naples': (17, 20),
    'Brussels': (20, 22)
}

flights_str = "Amsterdam and Warsaw, Helsinki and Brussels, Helsinki and Warsaw, Reykjavik and Brussels, Amsterdam and Lyon, Amsterdam and Naples, Amsterdam and Reykjavik, Naples and Valencia, Porto and Brussels, Amsterdam and Split, Lyon and Split, Warsaw and Split, Porto and Amsterdam, Helsinki and Split, Brussels and Lyon, Porto and Lyon, Reykjavik and Warsaw, Brussels and Valencia, Valencia and Lyon, Porto and Warsaw, Warsaw and Valencia, Amsterdam and Helsinki, Porto and Valencia, Warsaw and Brussels, Warsaw and Naples, Naples and Split, Helsinki and Naples, Helsinki and Reykjavik, Amsterdam and Valencia, Naples and Brussels"
flights_list = [edge.strip() for edge in flights_str.split(',')]
direct_set = set()
for edge in flights_list:
    parts = edge.split(' and ')
    if len(parts) == 2:
        c1, c2 = parts[0].strip(), parts[1].strip()
        direct_set.add((c1, c2))
        direct_set.add((c2, c1))

s = Solver()

a = {c: Int(f'a_{c}') for c in cities}
d = {c: Int(f'd_{c}') for c in cities}
pos = {c: Int(f'pos_{c}') for c in cities}

for c in cities:
    s.add(d[c] == a[c] + stays[c] - 1)

for c, (low, high) in events.items():
    s.add(a[c] <= high)
    s.add(d[c] >= low)

s.add([And(pos[c] >= 0, pos[c] < 10) for c in cities])
s.add(Distinct([pos[c] for c in cities]))

for c in cities:
    s.add(If(pos[c] == 0, a[c] == 1, True))
    s.add(If(pos[c] == 9, d[c] == 27, True))

for a_city in cities:
    for b_city in cities:
        if a_city == b_city:
            continue
        s.add(If(pos[b_city] == pos[a_city] + 1, d[a_city] == a[b_city], True))
        if (a_city, b_city) not in direct_set:
            s.add(pos[b_city] != pos[a_city] + 1)

if s.check() == sat:
    m = s.model()
    itinerary_list = []
    for day in range(1, 28):
        for city in cities:
            a_val = m.eval(a[city]).as_long()
            d_val = m.eval(d[city]).as_long()
            if a_val <= day <= d_val:
                itinerary_list.append({"day": day, "place": city})
    result = {'itinerary': itinerary_list}
    print(json.dumps(result))
else:
    print("No solution found")