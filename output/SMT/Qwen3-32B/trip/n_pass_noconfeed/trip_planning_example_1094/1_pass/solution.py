from z3 import *
import json

# Define cities and durations
cities = ['Paris', 'Vienna', 'Barcelona', 'Edinburgh', 'Krakow', 'Riga', 'Hamburg', 'Stockholm']
durations = [2, 4, 2, 4, 3, 4, 2, 2]

# Define allowed transitions
allowed_transitions = {
    (0, 7), (7, 0),  # Paris-Stockholm
    (1, 7), (7, 1),  # Vienna-Stockholm
    (0, 3), (3, 0),  # Paris-Edinburgh
    (5, 2), (2, 5),  # Riga-Barcelona
    (0, 5), (5, 0),  # Paris-Riga
    (4, 2), (2, 4),  # Krakow-Barcelona
    (3, 7), (7, 3),  # Edinburgh-Stockholm
    (0, 4), (4, 0),  # Paris-Krakow
    (4, 7), (7, 4),  # Krakow-Stockholm
    (5, 3), (3, 5),  # Riga-Edinburgh
    (2, 7), (7, 2),  # Barcelona-Stockholm
    (4, 3), (3, 4),  # Krakow-Edinburgh
    (1, 6), (6, 1),  # Vienna-Hamburg
    (0, 6), (6, 0),  # Paris-Hamburg
    (5, 7), (7, 5),  # Riga-Stockholm
    (6, 2), (2, 6),  # Hamburg-Barcelona
    (1, 2), (2, 1),  # Vienna-Barcelona
    (4, 1), (1, 4),  # Krakow-Vienna
    (5, 6), (6, 5),  # Riga-Hamburg
    (2, 3), (3, 2),  # Barcelona-Edinburgh
    (0, 2), (2, 0),  # Paris-Barcelona
    (6, 3), (3, 6),  # Hamburg-Edinburgh
    (0, 1), (1, 0),  # Paris-Vienna
    (1, 5), (5, 1),  # Vienna-Riga
    (6, 7), (7, 6),  # Hamburg-Stockholm
}

solver = Solver()

# Define order variables
order = [Int(f'order_{i}') for i in range(8)]
for o in order:
    solver.add(And(0 <= o, o <= 7))
solver.add(Distinct(order))
solver.add(order[0] == 0)  # Paris is first

# Define sum_d_so_far variables
sum_d_so_far = [Int(f'sum_d_{i}') for i in range(9)]
solver.add(sum_d_so_far[0] == 0)

# Helper function to get duration of a city index
def get_duration(city_index):
    return If(city_index == 0, 2,
              If(city_index == 1, 4,
                 If(city_index == 2, 2,
                    If(city_index == 3, 4,
                       If(city_index == 4, 3,
                          If(city_index == 5, 4,
                             If(city_index == 6, 2,
                                If(city_index == 7, 2, 0)))))))

# Add constraints for sum_d_so_far
for i in range(8):
    current_city = order[i]
    duration_expr = get_duration(current_city)
    solver.add(sum_d_so_far[i+1] == sum_d_so_far[i] + duration_expr)

# Define pos variables for each city
pos = [Int(f'pos_{i}') for i in range(8)]
for c in range(8):
    for i in range(8):
        solver.add(Implies(order[i] == c, pos[c] == i))

# Add constraints for specific cities
# Hamburg's start_day is 10 → sum_d_so_far[pos[6]] == 9
solver.add(sum_d_so_far[pos[6]] == 9)

# Edinburgh's start_day between 9 and 13
solver.add(And(9 <= 1 + sum_d_so_far[pos[3]], 1 + sum_d_so_far[pos[3]] <= 13))

# Stockholm's start_day is 14 or 15
solver.add(Or(1 + sum_d_so_far[pos[7]] == 14, 1 + sum_d_so_far[pos[7]] == 15))

# Add transition constraints
for i in range(7):
    current = order[i]
    next_c = order[i+1]
    allowed_expr = []
    for a, b in allowed_transitions:
        allowed_expr.append(And(current == a, next_c == b))
    solver.add(Or(allowed_expr))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    order_values = [model.evaluate(order[i]).as_long() for i in range(8)]
    
    # Compute sum_d_so_far values
    sum_d = [0] * 9
    for i in range(8):
        city_idx = order_values[i]
        sum_d[i+1] = sum_d[i] + durations[city_idx]
    
    # Generate itinerary
    itinerary = []
    for i in range(8):
        city_idx = order_values[i]
        start_day = 1 + sum_d[i]
        end_day = sum_d[i+1]
        city_name = cities[city_idx]
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city_name})
    
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")