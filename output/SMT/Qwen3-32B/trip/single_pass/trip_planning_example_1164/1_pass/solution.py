import z3

# Define cities and their durations
cities = ['Reykjavik', 'Stockholm', 'Porto', 'Nice', 'Venice', 'Vienna', 'Split', 'Copenhagen']
city_to_idx = {city: idx for idx, city in enumerate(cities)}
durations = {
    'Reykjavik': 2,
    'Stockholm': 2,
    'Porto': 5,
    'Nice': 3,
    'Venice': 4,
    'Vienna': 3,
    'Split': 3,
    'Copenhagen': 2,
}

# Define direct flight pairs and convert to indices
direct_flight_pairs = [
    ('Copenhagen', 'Vienna'),
    ('Nice', 'Stockholm'),
    ('Split', 'Copenhagen'),
    ('Nice', 'Reykjavik'),
    ('Nice', 'Porto'),
    ('Reykjavik', 'Vienna'),
    ('Stockholm', 'Copenhagen'),
    ('Nice', 'Venice'),
    ('Nice', 'Vienna'),
    ('Reykjavik', 'Copenhagen'),
    ('Nice', 'Copenhagen'),
    ('Stockholm', 'Vienna'),
    ('Venice', 'Vienna'),
    ('Copenhagen', 'Porto'),
    ('Reykjavik', 'Stockholm'),
    ('Stockholm', 'Split'),
    ('Split', 'Vienna'),
    ('Copenhagen', 'Venice'),
    ('Vienna', 'Porto'),
]

allowed_transitions = set()
for a, b in direct_flight_pairs:
    allowed_transitions.add((city_to_idx[a], city_to_idx[b]))
    allowed_transitions.add((city_to_idx[b], city_to_idx[a]))

# Initialize Z3 solver
s = z3.Solver()

# Define variables
order = [z3.Int(f'order_{i}') for i in range(8)]
start_day = [z3.Int(f'start_day_{i}') for i in range(8)]
pos = [z3.Int(f'pos_{c}') for c in range(8)]

# Constraints for order variables
for i in range(8):
    s.add(z3.And(0 <= order[i], order[i] <= 7))
s.add(z3.Distinct(order))

# Constraints for start_day variables
s.add(start_day[0] == 1)
for i in range(1, 8):
    prev_city_idx = order[i-1]
    duration_prev = durations[cities[prev_city_idx]]
    s.add(start_day[i] == start_day[i-1] + duration_prev - 1)

# Constraints for pos variables
for c in range(8):
    s.add(z3.And(0 <= pos[c], pos[c] <= 7))
    s.add(order[pos[c]] == c)

# Constraints for allowed transitions between consecutive cities
for i in range(7):
    current = order[i]
    next_c = order[i+1]
    constraints = []
    for a, b in allowed_transitions:
        constraints.append(z3.And(current == a, next_c == b))
    s.add(z3.Or(constraints))

# Event constraints
s.add(z3.And(2 <= start_day[pos[0]], start_day[pos[0]] <= 4))  # Reykjavik
s.add(z3.And(3 <= start_day[pos[1]], start_day[pos[1]] <= 5))  # Stockholm
s.add(z3.And(9 <= start_day[pos[2]], start_day[pos[2]] <= 17))  # Porto
s.add(z3.And(9 <= start_day[pos[5]], start_day[pos[5]] <= 13))  # Vienna

if s.check() == z3.sat:
    model = s.model()
    order_values = [model.eval(order[i]).as_long() for i in range(8)]
    start_day_values = [model.eval(start_day[i]).as_long() for i in range(8)]
    itinerary = {}
    for i in range(8):
        city_idx = order_values[i]
        city = cities[city_idx]
        duration = durations[city]
        start = start_day_values[i]
        for day in range(start, start + duration):
            itinerary[day] = city
    sorted_days = sorted(itinerary.keys())
    result = {'itinerary': [{'day': day, 'city': itinerary[day]} for day in sorted_days]}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")