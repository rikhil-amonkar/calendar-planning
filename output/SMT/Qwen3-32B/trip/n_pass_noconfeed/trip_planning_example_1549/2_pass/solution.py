from z3 import *
import json

# Define cities and their required durations
cities = ['Prague', 'Tallinn', 'Warsaw', 'Porto', 'Naples', 'Milan', 'Lisbon', 'Santorini', 'Riga', 'Stockholm']
durations = {
    'Prague': 5,
    'Tallinn': 3,
    'Warsaw': 2,
    'Porto': 3,
    'Naples': 5,
    'Milan': 3,
    'Lisbon': 5,
    'Santorini': 5,
    'Riga': 4,
    'Stockholm': 2
}

city_indices = {city: idx for idx, city in enumerate(cities)}

# Direct flights (bidirectional)
direct_flights = {
    ('Riga', 'Prague'), ('Stockholm', 'Milan'), ('Riga', 'Milan'), ('Lisbon', 'Stockholm'),
    ('Stockholm', 'Santorini'), ('Naples', 'Warsaw'), ('Lisbon', 'Warsaw'), ('Naples', 'Milan'),
    ('Lisbon', 'Naples'), ('Riga', 'Tallinn'), ('Tallinn', 'Prague'), ('Stockholm', 'Warsaw'),
    ('Riga', 'Warsaw'), ('Lisbon', 'Riga'), ('Riga', 'Stockholm'), ('Lisbon', 'Porto'), ('Lisbon', 'Prague'),
    ('Milan', 'Porto'), ('Prague', 'Milan'), ('Lisbon', 'Milan'), ('Warsaw', 'Porto'), ('Warsaw', 'Tallinn'),
    ('Santorini', 'Milan'), ('Stockholm', 'Prague'), ('Stockholm', 'Tallinn'), ('Warsaw', 'Milan'),
    ('Santorini', 'Naples'), ('Warsaw', 'Prague')
}

# Generate bidirectional transitions
allowed_transitions = []
for a, b in direct_flights:
    a_idx = city_indices[a]
    b_idx = city_indices[b]
    allowed_transitions.append((a_idx, b_idx))
    allowed_transitions.append((b_idx, a_idx))

# Create Z3 solver
solver = Solver()

# Sequence of cities (0-based indices)
seq = [Int(f'seq_{i}') for i in range(10)]

# Ensure all cities are used exactly once
for i in range(10):
    solver.add(And(0 <= seq[i], seq[i] < 10))
solver.add(Distinct(seq))

# Add constraints for direct flights between consecutive cities
for i in range(9):
    current = seq[i]
    next_city = seq[i+1]
    constraints = []
    for a, b in allowed_transitions:
        constraints.append(And(current == a, next_city == b))
    solver.add(Or(constraints))

# Create Z3 array for city durations
durations_z3 = Array('durations', IntSort(), IntSort())
for i in range(len(cities)):
    durations_z3 = Store(durations_z3, i, durations[cities[i]])

# Define cumulative duration sums
sum_durations = [Int(f'sum_durations_{i}') for i in range(11)]
solver.add(sum_durations[0] == 0)

for j in range(1, 11):
    # sum_durations[j] = sum_durations[j-1] + duration of city at position j-1
    duration_expr = durations_z3[seq[j-1]]
    solver.add(sum_durations[j] == sum_durations[j-1] + duration_expr)

# Add constraints for fixed start days
riga_idx = city_indices['Riga']
tallinn_idx = city_indices['Tallinn']
milan_idx = city_indices['Milan']

for j in range(10):
    solver.add(Implies(seq[j] == riga_idx, sum_durations[j] - (j-1) == 5))
    solver.add(Implies(seq[j] == tallinn_idx, sum_durations[j] - (j-1) == 18))
    solver.add(Implies(seq[j] == milan_idx, sum_durations[j] - (j-1) == 24))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    sequence = [model.eval(seq[i]).as_long() for i in range(10)]
    itinerary = []
    for i in range(10):
        city_idx = sequence[i]
        city_name = cities[city_idx]
        duration = durations[city_name]
        sum_d = model.eval(sum_durations[i]).as_long()
        start_day = sum_d - (i - 1)
        end_day = start_day + duration - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city_name})
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")