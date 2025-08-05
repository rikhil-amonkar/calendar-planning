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

e = [Int('e_%d' % i) for i in range(13)]

solver = Solver()

for i in range(13):
    solver.add(e[i] >= 0, e[i] <= 5)

madrid_idx = mapping['Madrid']
dublin_idx = mapping['Dublin']
oslo_idx = mapping['Oslo']
london_idx = mapping['London']
vilnius_idx = mapping['Vilnius']
berlin_idx = mapping['Berlin']

# Flight constraints
options0 = [e[0] == madrid_idx]
for (a, b) in flight_set:
    if a == madrid_idx:
        options0.append(e[0] == b)
solver.add(Or(options0))

for i in range(1, 13):
    options = [e[i] == e[i-1]]
    for (a, b) in flight_set:
        options.append(And(e[i-1] == a, e[i] == b))
    solver.add(Or(options))

# Consecutive nights for Madrid and London
solver.add(Or([And(e[i] == madrid_idx, e[i+1] == madrid_idx) for i in range(12)]))
solver.add(Or([And(e[i] == london_idx, e[i+1] == london_idx) for i in range(12)]))

# Counting constraints
city_counts = [0] * 6
for c in range(6):
    city_counts[c] = Sum([If(e[i] == c, 1, 0) for i in range(13)])
solver.add(city_counts[mapping['Dublin']] == 3)
solver.add(city_counts[mapping['Madrid']] == 2)
solver.add(city_counts[mapping['Oslo']] == 3)
solver.add(city_counts[mapping['London']] == 2)
solver.add(city_counts[mapping['Vilnius']] == 3)
solver.add(city_counts[mapping['Berlin']] == 5)

# Event constraints
solver.add(Or(e[5] == dublin_idx, e[6] == dublin_idx, e[7] == dublin_idx, e[8] == dublin_idx))
solver.add(Or(e[0] == madrid_idx, e[1] == madrid_idx))
solver.add(Or(e[1] == berlin_idx, e[2] == berlin_idx, e[3] == berlin_idx, 
              e[4] == berlin_idx, e[5] == berlin_idx, e[6] == berlin_idx))

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
    print("Plan found:", result)
else:
    print("No solution found")