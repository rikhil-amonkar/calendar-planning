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
    'Brussels': (18, 22)
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

s.add(a['Porto'] <= 5, d['Porto'] >= 1)
s.add(a['Amsterdam'] <= 8, d['Amsterdam'] >= 5)
s.add(a['Helsinki'] <= 11, d['Helsinki'] >= 8)
s.add(a['Naples'] <= 20, d['Naples'] >= 17)
s.add(a['Brussels'] <= 22, d['Brussels'] >= 18)

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

blocking_clause = Or(
    pos['Lyon'] != 0,
    pos['Porto'] != 1,
    pos['Amsterdam'] != 2,
    pos['Helsinki'] != 3,
    pos['Reykjavik'] != 4,
    pos['Brussels'] != 5,
    pos['Naples'] != 6,
    pos['Split'] != 7,
    pos['Warsaw'] != 8,
    pos['Valencia'] != 9
)
s.add(blocking_clause)

if s.check() == sat:
    m = s.model()
    a_vals = {c: m.eval(a[c]).as_long() for c in cities}
    d_vals = {c: m.eval(d[c]).as_long() for c in cities}
    pos_vals = {c: m.eval(pos[c]).as_long() for c in cities}
    
    sorted_cities = sorted(cities, key=lambda c: pos_vals[c])
    itinerary = []
    for c in sorted_cities:
        itinerary.append({'day_range': f'Day {a_vals[c]}-{d_vals[c]}', 'place': c})
    
    result = {'itinerary': itinerary}
    print(json.dumps(result))
else:
    s.pop()
    s.add(Not(blocking_clause))
    if s.check() == sat:
        m = s.model()
        a_vals = {c: m.eval(a[c]).as_long() for c in cities}
        d_vals = {c: m.eval(d[c]).as_long() for c in cities}
        pos_vals = {c: m.eval(pos[c]).as_long() for c in cities}
        
        sorted_cities = sorted(cities, key=lambda c: pos_vals[c])
        itinerary = []
        for c in sorted_cities:
            itinerary.append({'day_range': f'Day {a_vals[c]}-{d_vals[c]}', 'place': c})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")