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
    valid_flight = Or([And(location[d-1] == i, location[d] == j) for (i, j) in allowed_tuples])
    s.add(Implies(flight_taken[d-1], valid_flight))

madrid_idx = city_index['Madrid']
for d in range(6, 11):
    s.add(location[d] == madrid_idx)

venice_idx = city_index['Venice']
venice_days = []
for d in [4, 5, 6]:
    if d == 0:
        venice_days.append(location[d] == venice_idx)
    else:
        s1 = (location[d] == venice_idx)
        s2 = (location[d-1] == venice_idx)
        venice_days.append(Or(s1, s2) if flight_taken[d-1] else s1)
s.add(Or(venice_days))

totals = [0] * n_cities
totals[city_index['Brussels']] = 2
totals[city_index['Venice']] = 3
totals[city_index['London']] = 3
totals[city_index['Lisbon']] = 4
totals[city_index['Reykjavik']] = 3
totals[city_index['Santorini']] = 3
totals[city_index['Madrid']] = 5

for c in range(n_cities):
    count = 0
    count += If(location[0] == c, 1, 0)
    for d in range(1, n_days):
        if flight_taken[d-1]:
            count += If(location[d-1] == c, 1, 0)
            count += If(location[d] == c, 1, 0)
        else:
            count += If(location[d] == c, 1, 0)
    s.add(count == totals[c])

s.add(Sum([If(ft, 1, 0) for ft in flight_taken]) == 6)

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