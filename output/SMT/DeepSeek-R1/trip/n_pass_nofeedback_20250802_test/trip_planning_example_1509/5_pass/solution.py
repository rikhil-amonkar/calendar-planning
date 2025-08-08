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

order_array = Array('order', IntSort(), IntSort())
for i in range(10):
    s.add(order_array[i] >= 0, order_array[i] < 10)

s.add(Distinct([order_array[i] for i in range(10)]))

start_day_array = Array('start_day', IntSort(), IntSort())

s.add(start_day_array[order_array[0]] == 1)

for i in range(1, 10):
    prev_city = order_array[i-1]
    curr_city = order_array[i]
    s.add(start_day_array[curr_city] == start_day_array[prev_city] + days_list[prev_city] - 1)

for j in range(10):
    end_day = start_day_array[j] + days_list[j] - 1
    s.add(end_day <= 25)
    s.add(start_day_array[j] >= 1)

s.add(start_day_array[krakow_idx] == 17)
s.add(start_day_array[santorini_idx] == 12)
s.add(start_day_array[riga_idx] == 23)
s.add(start_day_array[paris_idx] <= 8)
s.add(start_day_array[helsinki_idx] >= 14)
s.add(start_day_array[helsinki_idx] <= 22)

for i in range(1, 10):
    prev = order_array[i-1]
    curr = order_array[i]
    edge_constraints = []
    for (u, v) in edges:
        edge_constraints.append(And(prev == u, curr == v))
    s.add(Or(edge_constraints))

if s.check() == sat:
    m = s.model()
    order_val = [m.evaluate(order_array[i]).as_long() for i in range(10)]
    start_day_val = [m.evaluate(start_day_array[j]).as_long() for j in range(10)]
    
    cities_per_day = {d: [] for d in range(1, 26)}
    for j in range(10):
        start = start_day_val[j]
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
                
    itinerary_entries.sort(key=lambda x: (x[0], x[2]))
    itinerary_list = [{"day_range": entry[3], "place": entry[2]} for entry in itinerary_entries]
    
    result = {'itinerary': itinerary_list}
    print(json.dumps(result))
else:
    print("No solution found")