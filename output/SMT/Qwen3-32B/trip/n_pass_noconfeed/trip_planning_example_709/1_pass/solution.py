import z3
import json

# Initialize the Z3 solver
solver = z3.Solver()

# Define cities and their durations
cities = ['Helsinki', 'Valencia', 'Dubrovnik', 'Porto', 'Prague', 'Reykjavik']
durations = [4, 5, 4, 3, 3, 4]  # Index 0-5

# Allowed direct flights (bidirectional)
allowed_pairs = [
    (0, 4), (4, 0),
    (4, 1), (1, 4),
    (1, 3), (3, 1),
    (0, 5), (5, 0),
    (2, 0), (0, 2),
    (5, 4), (4, 5)
]

# Create order variables
order = [z3.Int(f'order_{i}') for i in range(6)]

# Constraints: all distinct and in range 0-5
solver.add([z3.And(0 <= order[i], order[i] <= 5) for i in range(6)])
solver.add(z3.Distinct(order))

# Create sum_durs variables to track cumulative durations
sum_durs = [z3.Int(f'sum_durs_{i}') for i in range(7)]
solver.add(sum_durs[0] == 0)

for i in range(1, 7):
    # Determine duration of the (i-1)th city in the order
    dur_expr = z3.If(order[i-1] == 0, 4,
                     z3.If(order[i-1] == 1, 5,
                           z3.If(order[i-1] == 2, 4,
                                 z3.If(order[i-1] == 3, 3,
                                       z3.If(order[i-1] == 4, 3, 4))))
    solver.add(sum_durs[i] == sum_durs[i-1] + dur_expr)

# Add constraints for consecutive transitions
for i in range(5):  # 0 to 4
    current = order[i]
    next_c = order[i+1]
    conditions = []
    for (a, b) in allowed_pairs:
        conditions.append(z3.And(current == a, next_c == b))
    solver.add(z3.Or(conditions))

# Add constraints for Porto's end day (must be between 16-18)
for i in range(1, 7):  # 1-based position
    pos = i
    city = order[i-1]
    end_porto = sum_durs[pos] - (pos - 1)
    constraint = z3.Implies(city == 3, z3.And(16 <= end_porto, end_porto <= 18))
    solver.add(constraint)

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    order_vals = [model.eval(order[i]).as_long() for i in range(6)]
    
    # Generate the itinerary
    itinerary = []
    start_day = 1
    for city_idx in order_vals:
        city_name = cities[city_idx]
        duration = durations[city_idx]
        end_day = start_day + duration - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city_name})
        start_day = end_day  # Next city starts on the same day as previous ended
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")