import z3
import json

# List of cities and their durations
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

# Map city names to their durations
durations_by_index = [durations[cities[i]] for i in range(7)]

# Direct flights between cities
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

# Z3 solver setup
s = z3.Solver()

# Order of cities (0 to 6)
order = [z3.Int(f"order_{i}") for i in range(7)]

# Constraints: order is a permutation of 0 to 6
s.add([z3.And(order[i] >= 0, order[i] < 7) for i in range(7)])
s.add(z3.Distinct(order))

# Venice must be the first city
venice_idx = cities.index("Venice")
s.add(order[0] == venice_idx)

# Z3 array for durations
durations_z3 = z3.Array('durations', z3.IntSort(), z3.IntSort())
for i in range(7):
    s.add(durations_z3[i] == durations_by_index[i])

# Start days for each city
start_days = [z3.Int(f"start_{i}") for i in range(7)]
s.add(start_days[0] == 1)  # Venice starts on day 1

# Start day of each city is previous start + duration
for i in range(1, 7):
    prev_duration = durations_z3[order[i - 1]]
    s.add(start_days[i] == start_days[i - 1] + prev_duration)

# End day of the last city must be 24
last_duration = durations_z3[order[6]]
s.add(start_days[6] + last_duration - 1 == 24)

# Z3 array for allowed transitions
allowed_z3 = z3.Array('allowed', z3.IntSort(), z3.IntSort(), z3.BoolSort())
for i in range(7):
    for j in range(7):
        s.add(allowed_z3[i][j] == allowed[i][j])

# Ensure direct flight between consecutive cities
for i in range(6):
    curr = order[i]
    next_c = order[i + 1]
    s.add(allowed_z3[curr][next_c])

# Solve and print the itinerary
if s.check() == z3.sat:
    model = s.model()
    order_values = [model.eval(order[i]).as_long() for i in range(7)]
    start_days_values = [model.eval(start_days[i]).as_long() for i in range(7)]

    itinerary = []
    for i in range(7):
        city_idx = order_values[i]
        city_name = cities[city_idx]
        start_day = start_days_values[i]
        duration = durations_by_index[city_idx]
        end_day = start_day + duration - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city_name})

    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")