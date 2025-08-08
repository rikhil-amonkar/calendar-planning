from z3 import *

# City names in order: 0 to 9
city_names = [
    "Lisbon", "Prague", "Valencia", "Seville", "Paris",
    "Tallinn", "Oslo", "Lyon", "Nice", "Mykonos"
]

# Travel time matrix (symmetric)
travel_matrix = [
    [0, 2, 1, 1, 2, 3, 3, 2, 2, 3],  # Lisbon
    [2, 0, 2, 2, 1, 2, 2, 1, 2, 3],  # Prague
    [1, 2, 1, 1, 2, 3, 3, 2, 2, 3],  # Valencia
    [1, 2, 1, 0, 2, 3, 3, 2, 2, 3],  # Seville
    [2, 1, 2, 2, 0, 2, 2, 1, 2, 3],  # Paris
    [3, 2, 3, 3, 2, 0, 1, 2, 3, 3],  # Tallinn
    [3, 2, 3, 3, 2, 1, 0, 2, 3, 3],  # Oslo
    [2, 1, 2, 2, 1, 2, 2, 0, 1, 3],  # Lyon
    [2, 2, 2, 2, 2, 3, 3, 1, 0, 2],  # Nice
    [3, 3, 3, 3, 3, 3, 3, 3, 2, 0]   # Mykonos
]

# Create Z3 solver
s = Solver()

# Define the order of cities (permutation)
order = [Int(f'order_{i}') for i in range(10)]
for i in range(10):
    s.add(order[i] >= 0, order[i] < 10)
s.add(Distinct(order))

# Define stay durations for each city (each >= 2)
stay_durations = [Int(f'stay_{i}') for i in range(10)]
for i in range(10):
    s.add(stay_durations[i] >= 2)

# Define variables for travel times between consecutive cities
edge_travel = [Int(f'edge_travel_{k}') for k in range(9)]

# Add constraints to set edge_travel based on the order and travel_matrix
for k in range(9):
    cons = []
    for i in range(10):
        for j in range(10):
            cons.append(And(order[k] == i, order[k+1] == j, edge_travel[k] == travel_matrix[i][j]))
    s.add(Or(cons))

# Total travel time is the sum of edge_travel
total_travel = Sum(edge_travel)

# Total stay is the sum of stay_durations
total_stay = Sum([stay_durations[i] for i in range(10)])

# Constraint: total_stay + total_travel == 34
s.add(total_stay + total_travel == 34)

# Define stay_at_position: stay duration at each position in the order
stay_at_position = [Int(f'stay_pos_{i}') for i in range(10)]
for pos in range(10):
    cons_pos = []
    for i in range(10):
        cons_pos.append(And(order[pos] == i, stay_at_position[pos] == stay_durations[i]))
    s.add(Or(cons_pos))

# Define start days for each city in the order
start_days = [Int(f'start_{i}') for i in range(10)]
s.add(start_days[0] == 1)
for k in range(1, 10):
    s.add(start_days[k] == start_days[k-1] + stay_at_position[k-1] + edge_travel[k-1] - 1)

# Check and get the model
if s.check() == sat:
    model = s.model()
    order_vals = [model.evaluate(order[i]).as_long() for i in range(10)]
    stay_pos_vals = [model.evaluate(stay_at_position[i]).as_long() for i in range(10)]
    start_vals = [model.evaluate(start_days[i]).as_long() for i in range(10)]
    
    itinerary = []
    for i in range(10):
        city_index = order_vals[i]
        start_day = start_vals[i]
        end_day = start_vals[i] + stay_pos_vals[i] - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({
            'day_range': day_range,
            'place': city_names[city_index]
        })
    
    plan = {'itinerary': itinerary}
    print(f"Plan found: {plan}")
else:
    print("No valid plan found")