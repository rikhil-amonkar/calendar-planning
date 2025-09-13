import z3
import json

# Define cities and their durations
cities = ["Rome", "Munich", "Bucharest", "Riga", "Nice", "Mykonos", "Krakow"]
durations = [4, 4, 4, 3, 3, 3, 2]  # Index 0-6

# Define allowed direct flights as (from, to) pairs
allowed_transitions = [
    (4, 3), (3, 4),  # Nice-Riga
    (2, 1), (1, 2),  # Bucharest-Munich
    (5, 1), (1, 5),  # Mykonos-Munich
    (3, 2), (2, 3),  # Riga-Bucharest
    (0, 4), (4, 0),  # Rome-Nice
    (0, 1), (1, 0),  # Rome-Munich
    (5, 4), (4, 5),  # Mykonos-Nice
    (0, 5), (5, 0),  # Rome-Mykonos
    (1, 6), (6, 1),  # Munich-Krakow
    (0, 2), (2, 0),  # Rome-Bucharest
    (4, 1), (1, 4),  # Nice-Munich
    (3, 1),          # Riga to Munich
    (0, 3),          # Rome to Riga
]

# Create Z3 solver
solver = z3.Solver()

# Variables for permutation of cities
perm = [z3.Int(f'perm_{i}') for i in range(7)]

# Constraints: perm is a permutation of 0-6
solver.add(z3.Distinct(perm))
for i in range(7):
    solver.add(perm[i] >= 0, perm[i] <= 6)

# Variables for start days of each city in the sequence
start = [z3.Int(f'start_{i}') for i in range(7)]
solver.add(start[0] == 1)

# Define duration for each city
def get_duration(city_idx):
    return z3.If(city_idx == 0, 4,
                 z3.If(city_idx == 1, 4,
                       z3.If(city_idx == 2, 4,
                             z3.If(city_idx == 3, 3,
                                   z3.If(city_idx == 4, 3,
                                         z3.If(city_idx == 5, 3, 2)))))))

# Constraints for start days based on previous city's duration
for i in range(1, 7):
    duration_prev = get_duration(perm[i-1])
    solver.add(start[i] == start[i-1] + duration_prev - 1)

# Constraints for specific cities' day requirements
for i in range(7):
    duration_i = get_duration(perm[i])
    end_i = start[i] + duration_i - 1
    # Rome (index 0): must include day 1 and 4
    solver.add(z3.Implies(perm[i] == 0, z3.And(start[i] <= 1, end_i >= 4)))
    # Mykonos (index 5): must include days 4-6
    solver.add(z3.Implies(perm[i] == 5, z3.And(start[i] <= 4, end_i >= 6)))
    # Krakow (index 6): must include days 16-17
    solver.add(z3.Implies(perm[i] == 6, z3.And(start[i] <= 16, end_i >= 17)))

# Constraints for allowed transitions between consecutive cities
for i in range(6):
    current = perm[i]
    next_city = perm[i+1]
    allowed = [z3.And(current == a, next_city == b) for a, b in allowed_transitions]
    solver.add(z3.Or(allowed))

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    perm_values = [model.eval(perm[i]).as_long() for i in range(7)]
    start_values = [model.eval(start[i]).as_long() for i in range(7)]
    
    itinerary = []
    for i in range(7):
        city_index = perm_values[i]
        city_name = cities[city_index]
        s_day = start_values[i]
        duration = durations[city_index]
        e_day = s_day + duration - 1
        day_range = f"Day {s_day}-{e_day}"
        itinerary.append({"day_range": day_range, "place": city_name})
    
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"error": "No solution found"}))