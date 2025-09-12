from z3 import *
import json

# Define cities and their durations
cities = ['Riga', 'Brussels', 'Budapest', 'Rome', 'Dubrovnik', 'Geneva', 'Valencia']
durations = [4, 5, 2, 2, 3, 5, 2]

# Direct flights between cities (bidirectional)
allowed_transitions = {
    ('Brussels', 'Valencia'), ('Valencia', 'Brussels'),
    ('Rome', 'Valencia'), ('Valencia', 'Rome'),
    ('Brussels', 'Geneva'), ('Geneva', 'Brussels'),
    ('Rome', 'Geneva'), ('Geneva', 'Rome'),
    ('Dubrovnik', 'Geneva'), ('Geneva', 'Dubrovnik'),
    ('Valencia', 'Geneva'), ('Geneva', 'Valencia'),
    ('Rome', 'Riga'), ('Riga', 'Rome'),
    ('Geneva', 'Budapest'), ('Budapest', 'Geneva'),
    ('Riga', 'Brussels'), ('Brussels', 'Riga'),
    ('Rome', 'Budapest'), ('Budapest', 'Rome'),
    ('Rome', 'Brussels'), ('Brussels', 'Rome'),
    ('Brussels', 'Budapest'), ('Budapest', 'Brussels'),
    ('Dubrovnik', 'Rome'), ('Rome', 'Dubrovnik'),
}

# Precompute allowed transitions matrix
allowed_matrix = [[False] * 7 for _ in range(7)]
for a in range(7):
    for b in range(7):
        if (cities[a], cities[b]) in allowed_transitions:
            allowed_matrix[a][b] = True

# Create Z3 solver
solver = Solver()

# Create permutation variables for the 7 cities
perm = IntVector('perm', 7)
for i in range(7):
    solver.add(And(perm[i] >= 0, perm[i] <= 6))
solver.add(Distinct(perm))

# Compute start_day for each position
start_day = [Int(f'start_day_{i}') for i in range(7)]

for i in range(7):
    sum_expr = 0
    for j in range(i):
        # Compute duration for perm[j] using nested If statements
        duration_j = If(perm[j] == 0, 4,
                        If(perm[j] == 1, 5,
                           If(perm[j] == 2, 2,
                              If(perm[j] == 3, 2,
                                 If(perm[j] == 4, 3,
                                    If(perm[j] == 5, 5,
                                       If(perm[j] == 6, 2, 0)
                                       )
                                    )
                                 )
                             )
                         )
        sum_expr += (duration_j - 1)
    solver.add(start_day[i] == 1 + sum_expr)

# Add constraints for fixed start days
for i in range(7):
    # Riga (index 0) must have start_day ==4
    solver.add(If(perm[i] == 0, start_day[i] == 4, True == True))
    # Brussels (index 1) must have start_day ==7
    solver.add(If(perm[i] == 1, start_day[i] == 7, True == True))
    # Budapest (index 2) must have start_day ==16
    solver.add(If(perm[i] == 2, start_day[i] == 16, True == True))

# Add constraints for allowed transitions between consecutive cities
for i in range(6):
    current = perm[i]
    next_c = perm[i + 1]
    constraints = []
    for a in range(7):
        for b in range(7):
            if allowed_matrix[a][b]:
                constraints.append(And(current == a, next_c == b))
    solver.add(Or(constraints))

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    perm_values = [model.evaluate(perm[i]).as_long() for i in range(7)]
    start_day_values = [model.evaluate(start_day[i]).as_long() for i in range(7)]

    # Generate the itinerary
    itinerary = []
    for i in range(7):
        city_index = perm_values[i]
        city_name = cities[city_index]
        start = start_day_values[i]
        duration = durations[city_index]
        end = start + duration - 1
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city_name})

    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")