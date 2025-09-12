import z3
import json

# Define city codes and durations
cities = ['Vienna', 'Lyon', 'Edinburgh', 'Reykjavik', 'Stuttgart', 'Manchester', 'Split', 'Prague']
durations = [4, 3, 4, 5, 5, 2, 5, 4]
num_cities = len(cities)

# Allowed direct flights (city codes)
allowed_flights = set()
allowed_pairs = [
    (3,4), (4,3),  # Reykjavik-Stuttgart
    (4,6), (6,4),  # Stuttgart-Split
    (4,0), (0,4),  # Stuttgart-Vienna
    (7,5), (5,7),  # Prague-Manchester
    (2,7), (7,2),  # Edinburgh-Prague
    (5,6), (6,5),  # Manchester-Split
    (7,0), (0,7),  # Prague-Vienna
    (0,5), (5,0),  # Vienna-Manchester
    (7,6), (6,7),  # Prague-Split
    (0,1), (1,0),  # Vienna-Lyon
    (4,2), (2,4),  # Stuttgart-Edinburgh
    (6,1), (1,6),  # Split-Lyon
    (4,5), (5,4),  # Stuttgart-Manchester
    (7,1), (1,7),  # Prague-Lyon
    (3,0), (0,3),  # Reykjavik-Vienna
    (7,3), (3,7),  # Prague-Reykjavik
    (0,6), (6,0),  # Vienna-Split
]
for a, b in allowed_pairs:
    allowed_flights.add((a, b))

# Create Z3 solver
solver = z3.Solver()

# Create variables for positions and start days
pos = [z3.Int(f'pos_{i}') for i in range(num_cities)]
s = [z3.Int(f's_{i}') for i in range(num_cities)]

# Add constraints
# 1. All positions are distinct and in 0..7
solver.add(z3.Distinct(pos))
for i in range(num_cities):
    solver.add(pos[i] >= 0, pos[i] < num_cities)

# 2. s_0 == 1
solver.add(s[0] == 1)

# 3. s_{i+1} = s_i + durations[pos_i] - 1
for i in range(num_cities - 1):
    solver.add(s[i+1] == s[i] + durations[pos[i]] - 1)

# 4. end day of last city is 25
solver.add(s[num_cities - 1] + durations[pos[num_cities - 1]] - 1 == 25)

# 5. Edinburgh (code 2) must have start day 5
for i in range(num_cities):
    solver.add(z3.Implies(pos[i] == 2, s[i] == 5))

# 6. Split (code 6) must have start day between 15 and 21
for i in range(num_cities):
    solver.add(z3.Implies(pos[i] == 6, s[i] >= 15))
    solver.add(z3.Implies(pos[i] == 6, s[i] <= 21))

# 7. Consecutive cities must have direct flights
for i in range(num_cities - 1):
    current_city = pos[i]
    next_city = pos[i+1]
    flight_constraints = []
    for a, b in allowed_flights:
        flight_constraints.append(z3.And(current_city == a, next_city == b))
    solver.add(z3.Or(flight_constraints))

# Check if the constraints are satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    # Extract the order of cities
    order = []
    for i in range(num_cities):
        pos_val = model.evaluate(pos[i]).as_long()
        order.append(pos_val)
    # Now, get the start days for each position
    start_days = []
    for i in range(num_cities):
        start_days.append(model.evaluate(s[i]).as_long())
    # Now, create the itinerary
    itinerary = []
    for i in range(num_cities):
        city_code = order[i]
        city_name = cities[city_code]
        start_day = start_days[i]
        duration = durations[city_code]
        end_day = start_day + duration - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city_name})
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")