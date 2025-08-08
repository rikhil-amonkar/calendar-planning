from z3 import *
import json

cities = ['Salzburg', 'Venice', 'Bucharest', 'Brussels', 'Hamburg', 'Copenhagen', 'Nice', 'Zurich', 'Naples']

durations = {
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

flights = [
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

s = Solver()

# Create city index mapping
city_index = {city: idx for idx, city in enumerate(cities)}
index_city = {idx: city for idx, city in enumerate(cities)}

# Sequence variables (permutation of cities)
seq = [Int(f'seq_{i}') for i in range(9)]
for i in range(9):
    s.add(seq[i] >= 0, seq[i] < 9)
s.add(Distinct(seq))

# Start day variables
start_day = [Int(f'start_{city}') for city in cities]
for i, city in enumerate(cities):
    s.add(start_day[i] >= 1, start_day[i] <= 25)

# First city starts on day 1
s.add(Or([And(seq[0] == i, start_day[i] == 1) for i in range(9)]))

# End day calculation
end_day = [Int(f'end_{city}') for city in cities]
for i, city in enumerate(cities):
    s.add(end_day[i] == start_day[i] + durations[city] - 1)

# Order constraints between consecutive cities
for k in range(8):
    current_city = seq[k]
    next_city = seq[k+1]
    for i in range(9):
        for j in range(9):
            s.add(Implies(And(current_city == i, next_city == j), 
                         start_day[j] == end_day[i] + 1))

# Flight connection constraints
allowed_pairs = set()
for a, b in flights:
    allowed_pairs.add((a, b))
    allowed_pairs.add((b, a))

for k in range(8):
    current = seq[k]
    next_c = seq[k+1]
    constraints = []
    for city1 in cities:
        for city2 in cities:
            if (city1, city2) in allowed_pairs:
                i1, i2 = city_index[city1], city_index[city2]
                constraints.append(And(current == i1, next_c == i2))
    s.add(Or(constraints))

# Event date constraints
s.add(start_day[city_index['Brussels']] == 21)
s.add(And(start_day[city_index['Copenhagen']] >= 15, 
         start_day[city_index['Copenhagen']] <= 21))
s.add(And(start_day[city_index['Nice']] >= 7, 
         start_day[city_index['Nice']] <= 11))
s.add(And(start_day[city_index['Naples']] >= 19, 
         start_day[city_index['Naples']] <= 22))

# Total trip duration constraint
last_city = seq[8]
for i in range(9):
    s.add(Implies(last_city == i, end_day[i] <= 25))

if s.check() == sat:
    m = s.model()
    seq_val = [m.evaluate(seq[i]).as_long() for i in range(9)]
    start_vals = [m.evaluate(start_day[i]).as_long() for i in range(9)]
    
    # Build itinerary
    itinerary = []
    for pos in range(9):
        city_idx = seq_val[pos]
        city = cities[city_idx]
        start = start_vals[city_idx]
        dur = durations[city]
        for day in range(start, start + dur):
            itinerary.append({"day": day, "place": city})
    
    # Sort by day
    itinerary.sort(key=lambda x: x['day'])
    print(json.dumps({"itinerary": itinerary}))
else:
    print('{"itinerary": []}')