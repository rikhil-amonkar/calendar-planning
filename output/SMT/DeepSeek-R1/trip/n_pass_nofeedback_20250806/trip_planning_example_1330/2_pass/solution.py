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

city_index = {city: idx for idx, city in enumerate(cities)}
index_city = {idx: city for idx, city in enumerate(cities)}

seq = [Int(f'seq_{i}') for i in range(9)]
start_day_seq = [Int(f'start_day_{i}') for i in range(9)]

s.add(Distinct(seq))
for i in range(9):
    s.add(seq[i] >= 0)
    s.add(seq[i] < 9)

s.add(start_day_seq[0] == 1)

for i in range(8):
    dur_i = durations[index_city[seq[i].as_long()]]
    s.add(start_day_seq[i+1] == start_day_seq[i] + dur_i - 1)

start = {}
for city in cities:
    start_expr = None
    for pos in range(9):
        cond = (seq[pos] == city_index[city])
        if start_expr is None:
            start_expr = If(cond, start_day_seq[pos], -1)
        else:
            start_expr = If(cond, start_day_seq[pos], start_expr)
    start[city] = start_expr

s.add(start['Brussels'] == 21)

s.add(start['Copenhagen'] >= 15)
s.add(start['Copenhagen'] <= 21)

s.add(start['Nice'] >= 7)
s.add(start['Nice'] <= 11)

s.add(start['Naples'] >= 19)
s.add(start['Naples'] <= 22)

allowed_index_pairs = set()
for (a, b) in flights:
    idx_a = city_index[a]
    idx_b = city_index[b]
    allowed_index_pairs.add((idx_a, idx_b))
    allowed_index_pairs.add((idx_b, idx_a))

for i in range(8):
    constraints = []
    for (p0, p1) in allowed_index_pairs:
        constraints.append(And(seq[i] == p0, seq[i+1] == p1))
    s.add(Or(constraints))

last_city_dur = durations[index_city[seq[8].as_long()]]
s.add(start_day_seq[8] + last_city_dur - 1 <= 25)

if s.check() == sat:
    m = s.model()
    seq_vals = [m.evaluate(seq[i]).as_long() for i in range(9)]
    start_day_seq_vals = [m.evaluate(start_day_seq[i]).as_long() for i in range(9)]
    
    city_sequence = [index_city[idx] for idx in seq_vals]
    start_days = {}
    for i in range(9):
        city = index_city[seq_vals[i]]
        start_days[city] = start_day_seq_vals[i]
    
    itinerary = []
    for city in city_sequence:
        s_day = start_days[city]
        dur = durations[city]
        for d in range(s_day, s_day + dur):
            itinerary.append({"day": d, "place": city})
    
    result = {'itinerary': itinerary}
    print(json.dumps(result))
else:
    print('{"itinerary": []}')