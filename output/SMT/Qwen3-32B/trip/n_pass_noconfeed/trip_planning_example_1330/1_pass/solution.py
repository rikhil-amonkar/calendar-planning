import z3
import json

cities = ['Salzburg', 'Venice', 'Bucharest', 'Brussels', 'Hamburg', 'Copenhagen', 'Nice', 'Zurich', 'Naples']
durations = [2, 5, 4, 2, 4, 4, 3, 5, 4]

direct_flights = [
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
    ('Venice', 'Brussels'),
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
    ('Nice', 'Copenhagen'),
]

allowed_index_pairs = set()
for a, b in direct_flights:
    a_idx = cities.index(a)
    b_idx = cities.index(b)
    allowed_index_pairs.add((a_idx, b_idx))
    allowed_index_pairs.add((b_idx, a_idx))

s = z3.Solver()

# Variables for the sequence of cities (indices)
c = [z3.Int(f'c_{i}') for i in range(9)]

# All cities are distinct (permutation)
s.add(z3.Distinct(*c))

# For each consecutive pair, the flight must be allowed
for i in range(8):
    constraints = []
    for (a, b) in allowed_index_pairs:
        constraints.append(z3.And(c[i] == a, c[i+1] == b))
    s.add(z3.Or(constraints))

# Start days
start_day = [z3.Int(f'start_day_{i}') for i in range(9)]

# First day is 1
s.add(start_day[0] == 1)

# For each city in the sequence, start_day[i+1] = start_day[i] + duration of current city
for i in range(8):
    current_city_idx = c[i]
    duration = durations[current_city_idx]
    s.add(start_day[i+1] == start_day[i] + duration)

# Event constraints

# Visit relatives in Nice between day 9 and 11
nice_idx = cities.index('Nice')  # 6
for i in range(9):
    s.add(z3.Implies(c[i] == nice_idx, 
        z3.And(start_day[i] <= 11, start_day[i] >= 7)))

# Wedding in Copenhagen between day 18 and 21
cph_idx = cities.index('Copenhagen')  # 5
for i in range(9):
    s.add(z3.Implies(c[i] == cph_idx, 
        z3.And(start_day[i] <= 21, start_day[i] >= 15)))

# Meeting friends in Brussels between day 21 and 22
bru_idx = cities.index('Brussels')  # 3
for i in range(9):
    s.add(z3.Implies(c[i] == bru_idx, 
        z3.And(start_day[i] <= 22, start_day[i] >= 20)))

# Workshop in Naples between day 22 and 25
nap_idx = cities.index('Naples')  # 8
for i in range(9):
    s.add(z3.Implies(c[i] == nap_idx, 
        z3.And(start_day[i] <= 25, start_day[i] >= 19)))

# Check if the solver can find a solution
if s.check() == z3.sat:
    model = s.model()
    # Extract the sequence of cities
    sequence = [model.evaluate(c[i]).as_long() for i in range(9)]
    sequence_cities = [cities[sequence[i]] for i in range(9)]
    # Extract start days
    start_days = [model.evaluate(start_day[i]).as_long() for i in range(9)]
    # Generate the itinerary
    itinerary = []
    for i in range(9):
        start = start_days[i]
        duration = durations[sequence[i]]
        end = start + duration - 1
        city = sequence_cities[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")