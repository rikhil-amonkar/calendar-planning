from z3 import *
import json

cities = ['Salzburg', 'Venice', 'Bucharest', 'Brussels', 'Hamburg', 'Copenhagen', 'Nice', 'Zurich', 'Naples']
stays = {
    'Salzburg': 2,
    'Venice': 5,
    'Bucharest': 4,
    'Brussels': 2,
    'Hamburg': 4,
    'Copenhagen': 4,
    'Nice': 3,
    'Zurich': 5,
    'Naples': 4
}

event_constraints = {
    'Brussels': (21, 22),
    'Copenhagen': (18, 21),
    'Nice': (9, 11),
    'Naples': (22, 25)
}

direct_flights_list = [
    ('Zurich', 'Brussels'),
    ('Bucharest', 'Copenhagen'),
    ('Venice', 'Brussels'),
    ('Nice', 'Zurich'),
    ('Hamburg', 'Nice'),
    ('Zurich', 'Naples'),
    ('Hamburg', 'Bucharest'),
    ('Zurich', 'Copenhagen'),
    ('Bucharest', 'Brussels'),
    ('Hamburg', 'Brussels'),
    ('Venice', 'Naples'),
    ('Venice', 'Copenhagen'),
    ('Bucharest', 'Naples'),
    ('Hamburg', 'Copenhagen'),
    ('Venice', 'Zurich'),
    ('Nice', 'Brussels'),
    ('Hamburg', 'Venice'),
    ('Copenhagen', 'Naples'),
    ('Nice', 'Naples'),
    ('Hamburg', 'Zurich'),
    ('Salzburg', 'Hamburg'),
    ('Zurich', 'Bucharest'),
    ('Brussels', 'Naples'),
    ('Copenhagen', 'Brussels'),
    ('Venice', 'Nice'),
    ('Nice', 'Copenhagen')
]

direct_flights_set = set()
for a, b in direct_flights_list:
    direct_flights_set.add((a, b))
    direct_flights_set.add((b, a))

flight_ok = {}
for i, c1 in enumerate(cities):
    for j, c2 in enumerate(cities):
        flight_ok[(c1, c2)] = ( (c1, c2) in direct_flights_set )

s = Solver()

start = {}
end = {}
order = {}

for city in cities:
    start[city] = Int(f'start_{city}')
    end[city] = Int(f'end_{city}')
    order[city] = Int(f'order_{city}')

for city in cities:
    s.add(start[city] >= 1)
    s.add(end[city] <= 25)
    s.add(end[city] == start[city] + stays[city] - 1)

for city, (low, high) in event_constraints.items():
    s.add(start[city] <= high)
    s.add(end[city] >= low)

orders = [order[city] for city in cities]
s.add(Distinct(orders))
for city in cities:
    s.add(order[city] >= 0, order[city] < 9)

s.add(Or([And(order[city] == 0, start[city] == 1) for city in cities]))
s.add(Or([And(order[city] == 8, end[city] == 25) for city in cities]))

for i, city_i in enumerate(cities):
    for j, city_j in enumerate(cities):
        if city_i == city_j:
            continue
        if not flight_ok[(city_i, city_j)]:
            s.add(Not(order[city_j] == order[city_i] + 1))
        s.add(Implies(order[city_j] == order[city_i] + 1, 
                      end[city_i] == start[city_j]))

if s.check() == sat:
    model = s.model()
    starts = {}
    ends = {}
    orders_val = {}
    for city in cities:
        starts[city] = model.eval(start[city]).as_long()
        ends[city] = model.eval(end[city]).as_long()
        orders_val[city] = model.eval(order[city]).as_long()
    
    ordered_cities = sorted(cities, key=lambda city: orders_val[city])
    
    itinerary = []
    for idx, city in enumerate(ordered_cities):
        s_val = starts[city]
        e_val = ends[city]
        itinerary.append({
            "day_range": f"Day {s_val}-{e_val}",
            "place": city
        })
        if idx < len(ordered_cities) - 1:
            next_city = ordered_cities[idx+1]
            fly_day = e_val
            itinerary.append({
                "day_range": f"Day {fly_day}",
                "place": city
            })
            itinerary.append({
                "day_range": f"Day {fly_day}",
                "place": next_city
            })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print("No solution found")