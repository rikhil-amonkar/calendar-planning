import z3
import json

# Define cities and their indices
cities = ['Brussels', 'Venice', 'London', 'Lisbon', 'Reykjavik', 'Santorini', 'Madrid']
durations = [2, 3, 3, 4, 3, 3, 5]

# Allowed transitions
allowed_pairs = [
    (0,1), (1,0),
    (0,2), (2,0),
    (0,3), (3,0),
    (0,4), (4,0),
    (0,6), (6,0),
    (1,2), (2,1),
    (1,3), (3,1),
    (1,5), (5,1),
    (1,6), (6,1),
    (2,3), (3,2),
    (2,4), (4,2),
    (2,5), (5,2),
    (2,6), (6,2),
    (3,4), (4,3),
    (3,6), (6,3),
    (4,6),
    (5,6), (6,5),
]

s = z3.Solver()

# Create sequence variables: [0, c1, c2, c3, c4, c5, c6]
seq = [0] + [z3.Int(f'c{i}') for i in range(1,7)]

# Constraints: remaining cities are permutation of 1-6
s.add(z3.Distinct(seq[1:]))
for c in seq[1:]:
    s.add(z3.And(1 <= c, c <= 6))

# Constraints for allowed transitions between consecutive cities
for i in range(6):
    current = seq[i]
    next_city = seq[i+1]
    constraints = []
    for a, b in allowed_pairs:
        constraints.append(z3.And(current == a, next_city == b))
    s.add(z3.Or(constraints))

# Compute start_days for each segment
start_days = [z3.Int(f'start_day_{i}') for i in range(7)]
s.add(start_days[0] == 1)

for i in range(1, 7):
    prev_city = seq[i-1]
    duration_expr = z3.If(prev_city == 0, 2,
        z3.If(prev_city == 1, 3,
            z3.If(prev_city == 2, 3,
                z3.If(prev_city == 3, 4,
                    z3.If(prev_city == 4, 3,
                        z3.If(prev_city == 5, 3, 5))))))
    s.add(start_days[i] == start_days[i-1] + duration_expr - 1)

# Constraints for Venice (must be in days 5-7)
for j in range(7):
    s.add(z3.Implies(seq[j] == 1, z3.And(3 <= start_days[j], start_days[j] <= 7)))

# Constraints for Madrid (must be in days 7-11)
for j in range(7):
    s.add(z3.Implies(seq[j] == 6, z3.And(3 <= start_days[j], start_days[j] <= 11)))

# Check if the solver can find a solution
if s.check() == z3.sat:
    model = s.model()
    seq_values = [0] + [model.evaluate(c).as_long() for c in seq[1:]]
    start_days_values = [model.evaluate(start_days[i]).as_long() for i in range(7)]
    
    itinerary = {}
    for j in range(7):
        city_idx = seq_values[j]
        start = start_days_values[j]
        duration = durations[city_idx]
        end = start + duration - 1
        for day in range(start, end + 1):
            if day <= 17:
                itinerary[day] = cities[city_idx]
    
    output = {'itinerary': [{'day': day, 'city': itinerary[day]} for day in sorted(itinerary.keys())]}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")