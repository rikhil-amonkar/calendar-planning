from z3 import *
import json

cities = ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon']
days_list = [5, 2, 2, 2, 2, 5, 5, 5, 2, 4]

paris_idx = cities.index('Paris')
warsaw_idx = cities.index('Warsaw')
krakow_idx = cities.index('Krakow')
tallinn_idx = cities.index('Tallinn')
riga_idx = cities.index('Riga')
copenhagen_idx = cities.index('Copenhagen')
helsinki_idx = cities.index('Helsinki')
oslo_idx = cities.index('Oslo')
santorini_idx = cities.index('Santorini')
lyon_idx = cities.index('Lyon')

edges = set()
bidirectional = [
    ('Warsaw', 'Riga'),
    ('Warsaw', 'Tallinn'),
    ('Copenhagen', 'Helsinki'),
    ('Lyon', 'Paris'),
    ('Copenhagen', 'Warsaw'),
    ('Lyon', 'Oslo'),
    ('Paris', 'Oslo'),
    ('Paris', 'Riga'),
    ('Krakow', 'Helsinki'),
    ('Paris', 'Tallinn'),
    ('Oslo', 'Riga'),
    ('Krakow', 'Warsaw'),
    ('Paris', 'Helsinki'),
    ('Copenhagen', 'Santorini'),
    ('Helsinki', 'Warsaw'),
    ('Helsinki', 'Riga'),
    ('Copenhagen', 'Krakow'),
    ('Copenhagen', 'Riga'),
    ('Paris', 'Krakow'),
    ('Copenhagen', 'Oslo'),
    ('Oslo', 'Tallinn'),
    ('Oslo', 'Helsinki'),
    ('Copenhagen', 'Tallinn'),
    ('Paris', 'Copenhagen'),
    ('Paris', 'Warsaw'),
    ('Oslo', 'Krakow'),
    ('Helsinki', 'Tallinn')
]

directed = [
    ('Riga', 'Tallinn'),
    ('Santorini', 'Oslo')
]

for a, b in bidirectional:
    u = cities.index(a)
    v = cities.index(b)
    edges.add((u, v))
    edges.add((v, u))

for a, b in directed:
    u = cities.index(a)
    v = cities.index(b)
    edges.add((u, v))

s = Solver()

order = [Int('order_%d' % i) for i in range(10)]
for i in range(10):
    s.add(order[i] >= 0)
    s.add(order[i] < 10)
s.add(Distinct(order))

pos = [Int('pos_%d' % j) for j in range(10)]
for j in range(10):
    s.add(pos[j] >= 0)
    s.add(pos[j] < 10)
s.add(Distinct(pos))

for i in range(10):
    s.add(pos[order[i]] == i)

s_j = [Int('s_%d' % j) for j in range(10)]
for j in range(10):
    total = 0
    for k in range(10):
        total = total + If(pos[k] < pos[j], days_list[k] - 1, 0)
    s.add(s_j[j] == 1 + total)
    s.add(s_j[j] >= 1)
    s.add(s_j[j] + days_list[j] - 1 <= 25)

s.add(s_j[krakow_idx] == 17)
s.add(s_j[santorini_idx] == 12)
s.add(s_j[riga_idx] == 23)
s.add(s_j[paris_idx] <= 8)
s.add(s_j[helsinki_idx] >= 14)
s.add(s_j[helsinki_idx] <= 22)

edge_list = list(edges)
for i in range(9):
    cons_expr = Or([And(order[i] == u, order[i+1] == v) for (u, v) in edge_list])
    s.add(cons_expr)

if s.check() == sat:
    m = s.model()
    order_val = [m.evaluate(order[i]).as_long() for i in range(10)]
    s_val = [m.evaluate(s_j[j]).as_long() for j in range(10)]
    
    cities_per_day = {d: [] for d in range(1, 26)}
    for j in range(10):
        start = s_val[j]
        end = start + days_list[j] - 1
        for d in range(start, end + 1):
            if d <= 25:
                cities_per_day[d].append(cities[j])
    
    alone = {}
    for d in range(1, 26):
        for city in cities_per_day[d]:
            if len(cities_per_day[d]) == 1:
                alone[(city, d)] = True
            else:
                alone[(city, d)] = False
                
    itinerary_entries = []
    for j in range(10):
        city = cities[j]
        days = sorted([d for d in range(1, 26) if city in cities_per_day[d]])
        i = 0
        while i < len(days):
            d = days[i]
            if alone[(city, d)]:
                j_index = i
                while j_index < len(days) and days[j_index] == days[i] + (j_index - i) and alone[(city, days[j_index])]:
                    j_index += 1
                group_days = days[i:j_index]
                if len(group_days) == 1:
                    day_range_str = f"Day {group_days[0]}"
                else:
                    day_range_str = f"Day {group_days[0]}-{group_days[-1]}"
                itinerary_entries.append((group_days[0], group_days[-1], city, day_range_str))
                i = j_index
            else:
                day_range_str = f"Day {d}"
                itinerary_entries.append((d, d, city, day_range_str))
                i += 1
                
    itinerary_entries.sort(key=lambda x: (x[0], x[1], x[2]))
    itinerary_list = [{"day_range": entry[3], "place": entry[2]} for entry in itinerary_entries]
    
    result = {'itinerary': itinerary_list}
    print(json.dumps(result))
else:
    print("No solution found")