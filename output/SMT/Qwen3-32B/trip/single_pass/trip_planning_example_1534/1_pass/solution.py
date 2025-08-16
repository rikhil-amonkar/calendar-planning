from z3 import *

cities = ['Paris', 'Barcelona', 'Amsterdam', 'Warsaw', 'Venice', 'Vilnius', 'Salzburg', 'Hamburg', 'Florence', 'Tallinn']
city_ids = {city: idx for idx, city in enumerate(cities)}
durations = {
    'Paris': 2,
    'Barcelona': 5,
    'Amsterdam': 2,
    'Warsaw': 4,
    'Venice': 3,
    'Vilnius': 3,
    'Salzburg': 4,
    'Hamburg': 4,
    'Florence': 5,
    'Tallinn': 2
}

durations_list = [2,5,2,4,3,3,4,4,5,2]

direct_flights = set()
flights_list = [
    ('Paris', 'Venice'),
    ('Barcelona', 'Amsterdam'),
    ('Amsterdam', 'Warsaw'),
    ('Amsterdam', 'Vilnius'),
    ('Barcelona', 'Warsaw'),
    ('Warsaw', 'Venice'),
    ('Amsterdam', 'Hamburg'),
    ('Barcelona', 'Hamburg'),
    ('Barcelona', 'Florence'),
    ('Barcelona', 'Venice'),
    ('Paris', 'Hamburg'),
    ('Paris', 'Vilnius'),
    ('Paris', 'Amsterdam'),
    ('Paris', 'Florence'),
    ('Florence', 'Amsterdam'),
    ('Vilnius', 'Warsaw'),
    ('Barcelona', 'Tallinn'),
    ('Paris', 'Warsaw'),
    ('Tallinn', 'Warsaw'),
    ('Tallinn', 'Vilnius'),
    ('Amsterdam', 'Tallinn'),
    ('Paris', 'Tallinn'),
    ('Paris', 'Barcelona'),
    ('Venice', 'Hamburg'),
    ('Warsaw', 'Hamburg'),
    ('Hamburg', 'Salzburg'),
]

for a, b in flights_list:
    direct_flights.add((city_ids[a], city_ids[b]))
    direct_flights.add((city_ids[b], city_ids[a]))

s = Solver()

order = [Int(f'order_{i}') for i in range(10)]
for i in range(10):
    s.add(And(order[i] >= 0, order[i] <= 9))
s.add(Distinct(order))

def build_duration_expr(city_id_var):
    expr = 0
    for i in range(10):
        expr = If(city_id_var == i, durations_list[i], expr)
    return expr

start_days = [Int(f'start_day_{i}') for i in range(10)]
s.add(start_days[0] == 1)
for i in range(1, 10):
    prev_city_id = order[i-1]
    duration_expr = build_duration_expr(prev_city_id)
    s.add(start_days[i] == start_days[i-1] + duration_expr)

for i in range(9):
    current = order[i]
    next_c = order[i+1]
    allowed = []
    for a, b in direct_flights:
        allowed.append(And(current == a, next_c == b))
    s.add(Or(allowed))

for i in range(10):
    s.add(Implies(order[i] == 0, start_days[i] == 1))

for i in range(10):
    s.add(Implies(order[i] == 1, start_days[i] <= 6))

for i in range(10):
    s.add(Implies(order[i] == 6, And(start_days[i] >=19, start_days[i] <=22)))

for i in range(10):
    s.add(Implies(order[i] == 7, And(start_days[i] >=16, start_days[i] <=22)))

for i in range(10):
    s.add(Implies(order[i] == 9, And(start_days[i] >=10, start_days[i] <=12)))

if s.check() == sat:
    model = s.model()
    order_vals = [model[order[i]].as_long() for i in range(10)]
    start_day_vals = [model[start_days[i]].as_long() for i in range(10)]
    itinerary = {}
    for i in range(10):
        city_id = order_vals[i]
        city_name = cities[city_id]
        start = start_day_vals[i]
        duration = durations_list[city_id]
        for day in range(start, start + duration):
            itinerary[day] = city_name
    sorted_itinerary = sorted(itinerary.items())
    result = {'itinerary': [{'day': day, 'place': place} for day, place in sorted_itinerary]}
    print(result)
else:
    print("No solution found.")