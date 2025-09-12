from z3 import *
import json

# Define cities and their indices
cities = ['Reykjavik', 'Stuttgart', 'Munich', 'Geneva', 'Valencia', 'Seville', 'Istanbul', 'Vilnius']
durations_list = [4, 4, 3, 5, 5, 3, 4, 4]  # Duration for each city index

# Allowed transitions between cities (from, to)
allowed_transitions = [
    # From Reykjavik (0)
    [False, True, True, False, False, False, False, False],
    # From Stuttgart (1)
    [False, False, False, False, True, False, True, False],
    # From Munich (2)
    [False, False, False, True, True, True, True, False],
    # From Geneva (3)
    [False, False, True, False, True, False, True, False],
    # From Valencia (4)
    [False, False, True, True, False, True, True, False],
    # From Seville (5)
    [False, False, True, False, True, False, False, False],
    # From Istanbul (6)
    [False, True, True, True, True, False, False, True],
    # From Vilnius (7)
    [False, False, True, False, False, False, True, False]
]

# Z3 solver
solver = Solver()

# Variables for city order and start days
cities_order = [Int(f'city_{i}') for i in range(8)]
start_days = [Int(f'start_{i}') for i in range(8)]

# Constraint: All cities must be visited exactly once
solver.add(Distinct(cities_order))
for i in range(8):
    solver.add(And(cities_order[i] >= 0, cities_order[i] <= 7))

# Constraint: Start day of the first city is 1
solver.add(start_days[0] == 1)

# Constraint: Allowed transitions between consecutive cities
for i in range(7):
    prev_city = cities_order[i]
    next_city = cities_order[i + 1]
    allowed = False
    for p in range(8):
        for c in range(8):
            if allowed_transitions[p][c]:
                allowed = Or(allowed, And(prev_city == p, next_city == c))
    solver.add(allowed)

# Constraint: Fixed start days for specific cities
fixed_start = {0: 1, 1: 4, 2: 13, 6: 19}  # city index: start day
for city_idx, fixed_day in fixed_start.items():
    for i in range(8):
        solver.add(If(cities_order[i] == city_idx, start_days[i] == fixed_day, True))

# Helper function to get duration based on city index
def get_duration_expr(city_var):
    expr = 0
    for idx, d in enumerate(durations_list):
        expr = If(city_var == idx, d, expr)
    return expr

# Constraints for end days and final day
for i in range(8):
    duration_i = get_duration_expr(cities_order[i])
    end_day_i = start_days[i] + duration_i - 1
    if i < 7:
        solver.add(start_days[i + 1] == end_day_i)
    else:
        solver.add(end_day_i == 25)

# Solve and generate output
if solver.check() == sat:
    model = solver.model()
    cities_order_vals = [model.evaluate(c).as_long() for c in cities_order]
    start_days_vals = [model.evaluate(s).as_long() for s in start_days]
    itinerary = []
    for i in range(8):
        city_idx = cities_order_vals[i]
        city_name = cities[city_idx]
        start_day = start_days_vals[i]
        duration = durations_list[city_idx]
        end_day = start_day + duration - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city_name})
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")