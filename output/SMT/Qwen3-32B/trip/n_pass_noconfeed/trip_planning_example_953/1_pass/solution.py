import z3
import json

cities = ["Venice", "Salzburg", "Stockholm", "Frankfurt", "Florence", "Barcelona", "Stuttgart"]
durations = {
    "Venice": 5,
    "Salzburg": 4,
    "Stockholm": 2,
    "Frankfurt": 4,
    "Florence": 4,
    "Barcelona": 2,
    "Stuttgart": 3
}

direct_flights = {
    ("Barcelona", "Frankfurt"),
    ("Frankfurt", "Barcelona"),
    ("Florence", "Frankfurt"),
    ("Frankfurt", "Florence"),
    ("Stockholm", "Barcelona"),
    ("Barcelona", "Stockholm"),
    ("Venice", "Barcelona"),
    ("Barcelona", "Venice"),
    ("Stuttgart", "Barcelona"),
    ("Barcelona", "Stuttgart"),
    ("Frankfurt", "Salzburg"),
    ("Salzburg", "Frankfurt"),
    ("Stockholm", "Frankfurt"),
    ("Frankfurt", "Stockholm"),
    ("Stuttgart", "Stockholm"),
    ("Stockholm", "Stuttgart"),
    ("Stuttgart", "Frankfurt"),
    ("Frankfurt", "Stuttgart"),
    ("Venice", "Stuttgart"),
    ("Stuttgart", "Venice"),
    ("Venice", "Frankfurt"),
    ("Frankfurt", "Venice"),
}

# Precompute allowed matrix
allowed = [[False for _ in range(7)] for _ in range(7)]
for (a, b) in direct_flights:
    idx_a = cities.index(a)
    idx_b = cities.index(b)
    allowed[idx_a][idx_b] = True

allowed_pairs = []
for i in range(7):
    for j in range(7):
        if allowed[i][j]:
            allowed_pairs.append((i, j))

s = z3.Solver()

# Variables for order
order = [z3.Int(f"order_{i}") for i in range(7)]

# Constraints for order variables to be 0-6 and distinct
s.add([z3.And(order[i] >= 0, order[i] < 7) for i in range(7)])
s.add(z3.Distinct(order))

# Durations array
durations_by_index = [durations[cities[i]] for i in range(7)]
durations_z3 = z3.Array('durations', z3.IntSort(), z3.IntSort())
for i in range(7):
    s.add(durations_z3[i] == durations_by_index[i])

# Variables for start days
start_days = [z3.Int(f"start_{i}") for i in range(7)]
s.add(start_days[0] >= 1)

# Constraints for start_days
for i in range(1, 7):
    prev_duration = z3.Select(durations_z3, order[i-1])
    s.add(start_days[i] == start_days[i-1] + prev_duration - 1)

# End day of last city is 18
last_duration = z3.Select(durations_z3, order[6])
s.add(start_days[6] + last_duration - 1 == 18)

# Venice must start on day 1
venice_idx = cities.index("Venice")
venice_positions = []
for k in range(7):
    venice_positions.append(z3.And(order[k] == venice_idx, start_days[k] == 1))
s.add(z3.Or(venice_positions))

# Direct flight constraints
for i in range(6):
    curr = order[i]
    next_c = order[i+1]
    constraints = []
    for (curr_p, next_p) in allowed_pairs:
        constraints.append(z3.And(curr == curr_p, next_c == next_p))
    s.add(z3.Or(constraints))

# Check if the solver can find a solution
if s.check() == z3.sat:
    model = s.model()
    # Extract order and start_days
    order_values = [model.eval(order[i]).as_long() for i in range(7)]
    start_days_values = [model.eval(start_days[i]).as_long() for i in range(7)]
    
    # Build the itinerary
    itinerary = []
    for i in range(7):
        city_idx = order_values[i]
        city_name = cities[city_idx]
        start_day = start_days_values[i]
        duration = durations_by_index[city_idx]
        end_day = start_day + duration - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city_name})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")