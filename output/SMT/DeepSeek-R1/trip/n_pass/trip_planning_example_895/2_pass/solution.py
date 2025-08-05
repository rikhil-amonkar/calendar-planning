from z3 import *
import json

city_names = ['Brussels', 'Venice', 'London', 'Lisbon', 'Reykjavik', 'Santorini', 'Madrid']
n_cities = len(city_names)
n_days = 17

city_index = {name: idx for idx, name in enumerate(city_names)}

directed_flights = set()
bidir = [
    ('Venice', 'Madrid'),
    ('Lisbon', 'Reykjavik'),
    ('Brussels', 'Venice'),
    ('Venice', 'Santorini'),
    ('Lisbon', 'Venice'),
    ('Brussels', 'London'),
    ('Madrid', 'London'),
    ('Santorini', 'London'),
    ('London', 'Reykjavik'),
    ('Brussels', 'Lisbon'),
    ('Lisbon', 'London'),
    ('Lisbon', 'Madrid'),
    ('Madrid', 'Santorini'),
    ('Brussels', 'Reykjavik'),
    ('Brussels', 'Madrid'),
    ('Venice', 'London')
]
for (a, b) in bidir:
    directed_flights.add((a, b))
    directed_flights.add((b, a))
directed_flights.add(('Reykjavik', 'Madrid'))

flight_ok = [[False] * n_cities for _ in range(n_cities)]
for i in range(n_cities):
    for j in range(n_cities):
        if i != j:
            if (city_names[i], city_names[j]) in directed_flights:
                flight_ok[i][j] = True

s = Solver()

location = [Int(f'loc_{d}') for d in range(n_days)]
for d in range(n_days):
    s.add(location[d] >= 0, location[d] < n_cities)

flight_taken = [Bool(f'fly_{d}') for d in range(1, n_days)]

s.add(location[0] == city_index['Brussels'])

for d in range(1, n_days):
    s.add(flight_taken[d-1] == (location[d-1] != location[d]))
    a = location[d-1]
    b = location[d]
    s.add(Implies(flight_taken[d-1], flight_ok[a][b]))

brussels_idx = city_index['Brussels']
s.add(Or(location[1] == brussels_idx, flight_taken[0]))

madrid_idx = city_index['Madrid']
for d in [6,7,8,9,10]:
    if d == 0:
        s.add(location[0] == madrid_idx)
    else:
        s.add(Or(location[d] == madrid_idx, And(flight_taken[d-1], location[d-1] == madrid_idx)))

venice_idx = city_index['Venice']
in_venice = []
for d in range(n_days):
    if d == 0:
        in_venice.append(location[0] == venice_idx)
    else:
        in_venice.append(Or(location[d] == venice_idx, And(flight_taken[d-1], location[d-1] == venice_idx)))
s.add(Or(in_venice[4], in_venice[5], in_venice[6]))
s.add(Sum([If(cond, 1, 0) for cond in in_venice]) == 3)

totals = [0] * n_cities
totals[city_index['Brussels']] = 2
totals[city_index['Venice']] = 3
totals[city_index['London']] = 3
totals[city_index['Lisbon']] = 4
totals[city_index['Reykjavik']] = 3
totals[city_index['Santorini']] = 3
totals[city_index['Madrid']] = 5

for c in range(n_cities):
    in_city_c = []
    for d in range(n_days):
        if d == 0:
            in_city_c.append(location[0] == c)
        else:
            in_city_c.append(Or(location[d] == c, And(flight_taken[d-1], location[d-1] == c)))
    s.add(Sum([If(cond, 1, 0) for cond in in_city_c]) == totals[c])

if s.check() == sat:
    m = s.model()
    itinerary = []
    for d in range(n_days):
        if d == 0:
            city0 = m[location[0]].as_long()
            places = [city_names[city0]]
        else:
            if m[flight_taken[d-1]]:
                city_prev = m[location[d-1]].as_long()
                city_curr = m[location[d]].as_long()
                places = [city_names[city_prev], city_names[city_curr]]
            else:
                city_curr = m[location[d]].as_long()
                places = [city_names[city_curr]]
        itinerary.append({"day": d+1, "place": places})
    print(json.dumps({'itinerary': itinerary}))
else:
    print("No solution found")