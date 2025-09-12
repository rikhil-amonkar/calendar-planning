import z3
import json

# Define the cities and their durations
# 0: Reykjavik, 1: Stockholm, 2: Porto, 3: Nice, 4: Venice, 5: Vienna, 6: Split, 7: Copenhagen
durations = [2, 2, 5, 3, 4, 3, 3, 2]

# Allowed direct flights as pairs of city indices (both directions)
allowed_flights = [
    (7, 5), (5, 7),  # Copenhagen-Vienna
    (3, 1), (1, 3),  # Nice-Stockholm
    (6, 7), (7, 6),  # Split-Copenhagen
    (3, 0), (0, 3),  # Nice-Reykjavik
    (3, 2), (2, 3),  # Nice-Porto
    (0, 5), (5, 0),  # Reykjavik-Vienna
    (1, 7), (7, 1),  # Stockholm-Copenhagen
    (3, 4), (4, 3),  # Nice-Venice
    (3, 5), (5, 3),  # Nice-Vienna
    (0, 7), (7, 0),  # Reykjavik-Copenhagen
    (3, 7), (7, 3),  # Nice-Copenhagen
    (1, 5), (5, 1),  # Stockholm-Vienna
    (4, 5), (5, 4),  # Venice-Vienna
    (7, 2), (2, 7),  # Copenhagen-Porto
    (0, 1), (1, 0),  # Reykjavik-Stockholm
    (1, 6), (6, 1),  # Stockholm-Split
    (6, 5), (5, 6),  # Split-Vienna
    (7, 4), (4, 7),  # Copenhagen-Venice
    (5, 2), (2, 5),  # Vienna-Porto
]

# Z3 solver setup
solver = z3.Solver()

# Variables for the order of cities (permutation of 0-7)
order = [z3.Int(f'order_{i}') for i in range(8)]

# Constraints: all cities are unique and in range 0-7
solver.add([z3.And(0 <= order[i], order[i] <= 7) for i in range(8)])
solver.add(z3.Distinct(order))

# Variables for start days of each city in the order
start_day = [z3.Int(f'start_day_{i}') for i in range(8)]
solver.add(start_day[0] == 1)

# Create Z3 array for durations
durations_array = z3.Array('durations_array', z3.IntSort(), z3.IntSort())
for idx in range(8):
    solver.add(durations_array[idx] == durations[idx])

# Compute start day for each city based on previous city's duration
for i in range(1, 8):
    solver.add(start_day[i] == start_day[i-1] + z3.Select(durations_array, order[i-1]) - 1)

# Constraints for fixed start days and ranges
for i in range(8):
    # Reykjavik (0) must start on day 3
    solver.add(z3.Implies(order[i] == 0, start_day[i] == 3))
    # Stockholm (1) must start on day 4
    solver.add(z3.Implies(order[i] == 1, start_day[i] == 4))
    # Porto (2) must have start_day between 9 and 13
    solver.add(z3.Implies(order[i] == 2, z3.And(start_day[i] >= 9, start_day[i] <= 13)))
    # Vienna (5) must have start_day between 9 and 11
    solver.add(z3.Implies(order[i] == 5, z3.And(start_day[i] >= 9, start_day[i] <= 11)))

# Constraints for allowed flights between consecutive cities
for i in range(7):
    allowed_pairs = [z3.And(order[i] == x, order[i+1] == y) for x, y in allowed_flights]
    solver.add(z3.Or(*allowed_pairs))

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    order_values = [model.evaluate(order[i]).as_long() for i in range(8)]
    start_day_values = [model.evaluate(start_day[i]).as_long() for i in range(8)]

    # Map city indices to names
    city_names = {
        0: "Reykjavik",
        1: "Stockholm",
        2: "Porto",
        3: "Nice",
        4: "Venice",
        5: "Vienna",
        6: "Split",
        7: "Copenhagen"
    }

    # Build the itinerary
    itinerary = []
    for i in range(8):
        city_idx = order_values[i]
        start = start_day_values[i]
        dur = durations[city_idx]
        end = start + dur - 1
        city_name = city_names[city_idx]
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city_name
        })

    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"error": "No solution found"}))