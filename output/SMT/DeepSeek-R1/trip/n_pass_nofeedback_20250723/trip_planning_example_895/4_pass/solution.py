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

allowed_tuples = []
for i in range(n_cities):
    for j in range(n_cities):
        if (city_names[i], city_names[j]) in directed_flights:
            allowed_tuples.append((i, j))

s = Solver()

location = [Int(f'loc_{d}') for d in range(n_days)]
for d in range(n_days):
    s.add(location[d] >= 0, location[d] < n_cities)

flight_taken = [Bool(f'fly_{d}') for d in range(1, n_days)]

s.add(location[0] == city_index['Brussels'])
s.add(location[1] == city_index['Brussels'])

for d in range(1, n_days):
    s.add(flight_taken[d-1] == (location[d-1] != location[d]))
    disj = []
    for (i, j) in allowed_tuples:
        disj.append(And(location[d-1] == i, location[d] == j))
    s.add(Implies(flight_taken[d-1], Or(disj)))

madrid_idx = city_index['Madrid']
for d in range(6, 11):  # Days 7-11 (indices 6-10)
    s.add(location[d] == madrid_idx)

venice_idx = city_index['Venice']
s.add(Or(location[4] == venice_idx, location[5] == venice_idx, location[6] == venice_idx))

totals = [0] * n_cities
totals[city_index['Brussels']] = 2
totals[city_index['Venice']] = 3
totals[city_index['London']] = 3
totals[city_index['Lisbon']] = 4
totals[city_index['Reykjavik']] = 3
totals[city_index['Santorini']] = 3
totals[city_index['Madrid']] = 5

for c in range(n_cities):
    s.add(Sum([If(location[d] == c, 1, 0) for d in range(n_days)]) == totals[c])

if s.check() == sat:
    m = s.model()
    itinerary = []
    for d in range(n_days):
        city_id = m[location[d]].as_long()
        city_name = city_names[city_id]
        places = [city_name]
        if d > 0 and m[flight_taken[d-1]]:
            prev_city_id = m[location[d-1]].as_long()
            if prev_city_id != city_id:
                places = [city_names[prev_city_id], city_name]
        itinerary.append({"day": d+1, "place": places})
    print(json.dumps({'itinerary': itinerary}))
else:
    print("No solution found")