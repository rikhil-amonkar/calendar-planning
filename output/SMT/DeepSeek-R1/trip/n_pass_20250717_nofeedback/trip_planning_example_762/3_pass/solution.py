from z3 import *

cities = ['Dublin', 'Madrid', 'Oslo', 'London', 'Vilnius', 'Berlin']
mapping = {city: idx for idx, city in enumerate(cities)}
rev_mapping = {idx: city for idx, city in enumerate(cities)}

flights = [
    ('London', 'Madrid'),
    ('Oslo', 'Vilnius'),
    ('Berlin', 'Vilnius'),
    ('Madrid', 'Oslo'),
    ('Madrid', 'Dublin'),
    ('London', 'Oslo'),
    ('Madrid', 'Berlin'),
    ('Berlin', 'Oslo'),
    ('Dublin', 'Oslo'),
    ('London', 'Dublin'),
    ('London', 'Berlin'),
    ('Berlin', 'Dublin')
]

flight_set = set()
for flight in flights:
    a, b = flight
    a_idx = mapping[a]
    b_idx = mapping[b]
    flight_set.add((a_idx, b_idx))
    flight_set.add((b_idx, a_idx))

s = [Int('s_%d' % i) for i in range(1, 14)]
e = [Int('e_%d' % i) for i in range(1, 14)]

solver = Solver()

for i in range(13):
    solver.add(s[i] >= 0, s[i] <= 5)
    solver.add(e[i] >= 0, e[i] <= 5)

for i in range(1, 13):
    solver.add(s[i] == e[i-1])

flight_list = list(flight_set)
for i in range(13):
    same_city = (s[i] == e[i])
    options = [And(s[i] == a, e[i] == b) for (a, b) in flight_list]
    solver.add(Or(same_city, *options))

city_days = [0] * 6
for c_idx in range(6):
    start_days = Sum([If(s[i] == c_idx, 1, 0) for i in range(13)])
    end_days = Sum([If(And(e[i] == c_idx, s[i] != c_idx), 1, 0) for i in range(13)])
    city_days[c_idx] = start_days + end_days

solver.add(city_days[mapping['Dublin']] == 3)
solver.add(city_days[mapping['Madrid']] == 2)
solver.add(city_days[mapping['Oslo']] == 3)
solver.add(city_days[mapping['London']] == 2)
solver.add(city_days[mapping['Vilnius']] == 3)
solver.add(city_days[mapping['Berlin']] == 5)

dublin_idx = mapping['Dublin']
solver.add(Or(
    Or(s[6] == dublin_idx, e[6] == dublin_idx),
    Or(s[7] == dublin_idx, e[7] == dublin_idx),
    Or(s[8] == dublin_idx, e[8] == dublin_idx)
))

madrid_idx = mapping['Madrid']
solver.add(Or(
    Or(s[1] == madrid_idx, e[1] == madrid_idx),
    Or(s[2] == madrid_idx, e[2] == madrid_idx)
))

berlin_idx = mapping['Berlin']
solver.add(Or(
    Or(s[2] == berlin_idx, e[2] == berlin_idx),
    Or(s[3] == berlin_idx, e[3] == berlin_idx),
    Or(s[4] == berlin_idx, e[4] == berlin_idx),
    Or(s[5] == berlin_idx, e[5] == berlin_idx),
    Or(s[6] == berlin_idx, e[6] == berlin_idx)
))

for city in ['Madrid', 'London']:
    c_idx = mapping[city]
    consecutive_days = []
    for i in range(12):
        consecutive_days.append(Or(
            And(s[i] == c_idx, s[i+1] == c_idx),
            And(s[i] == c_idx, e[i+1] == c_idx),
            And(e[i] == c_idx, s[i+1] == c_idx),
            And(e[i] == c_idx, e[i+1] == c_idx)
        ))
    solver.add(Or(consecutive_days))

if solver.check() == sat:
    model = solver.model()
    end_cities = [model.evaluate(e[i]).as_long() for i in range(13)]
    itinerary = []
    i = 0
    while i < 13:
        j = i
        current_city = end_cities[i]
        while j < 13 and end_cities[j] == current_city:
            j += 1
        start_day = i + 1
        end_day = j
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        itinerary.append({'day_range': day_range, 'place': rev_mapping[current_city]})
        i = j
    result = {'itinerary': itinerary}
    print(result)
else:
    print("No solution found")