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

s.add(a['Porto'] >= 1, a['Porto'] <= 5)
s.add(a['Amsterdam'] >= 2, a['Amsterdam'] <= 8)
s.add(a['Helsinki'] >= 5, a['Helsinki'] <= 11)
s.add(a['Naples'] >= 14, a['Naples'] <= 20)
s.add(a['Brussels'] >= 18, a['Brussels'] <= 22)

s.add([And(pos[c] >= 0, pos[c] < 10) for c in cities])
s.add(Distinct([pos[c] for c in cities]))

first_city = Or([And(pos[c] == 0, a[c] == 1) for c in cities])
last_city = Or([And(pos[c] == 9, d[c] == 27) for c in cities])
s.add(first_city, last_city)

for i in range(len(cities)):
    for j in range(len(cities)):
        if i == j:
            continue
        A = cities[i]
        B = cities[j]
        cond = pos[A] < pos[B]
        consecutive = pos[B] == pos[A] + 1
        s.add(If(cond, 
                 If(consecutive, 
                    And(d[A] == a[B], (A, B) in direct_set), 
                    d[A] < a[B]),
                 True))

for c in cities:
    s.add(a[c] >= 1)
    s.add(d[c] <= 27)

if s.check() == sat:
    m = s.model()
    itinerary_list = []
    for day in range(1, 28):
        for c in cities:
            a_val = m.eval(a[c]).as_long()
            d_val = m.eval(d[c]).as_long()
            if a_val <= day <= d_val:
                itinerary_list.append({"day": day, "place": c})
    result = {'itinerary': itinerary_list}
    print(json.dumps(result))
else:
    print("No solution found")