import z3
import json

# Define city codes
HAMBURG = 0
ZURICH = 1
HEL = 2
BUCHAREST = 3
SPLIT = 4

city_durations = {
    HAMBURG: 2,
    ZURICH: 3,
    HEL: 2,
    BUCHAREST: 2,
    SPLIT: 7
}

city_names = {
    HAMBURG: "Hamburg",
    ZURICH: "Zurich",
    HEL: "Helsinki",
    BUCHAREST: "Bucharest",
    SPLIT: "Split"
}

allowed_pairs = [
    (HAMBURG, BUCHAREST), (BUCHAREST, HAMBURG),
    (HAMBURG, HEL), (HEL, HAMBURG),
    (ZURICH, HAMBURG), (HAMBURG, ZURICH),
    (ZURICH, HEL), (HEL, ZURICH),
    (ZURICH, BUCHAREST), (BUCHAREST, ZURICH),
    (ZURICH, SPLIT), (SPLIT, ZURICH),
    (HEL, SPLIT), (SPLIT, HEL),
    (SPLIT, HAMBURG), (HAMBURG, SPLIT),
]

solver = z3.Solver()

# Create order variables
order = [z3.Int(f'order_{i}') for i in range(5)]

# Add constraints: all distinct and between 0-4
solver.add([z3.And(order[i] >= 0, order[i] <= 4) for i in range(5)])
solver.add(z3.Distinct(order))

# Create start_day variables
start_days = [z3.Int(f'start_{i}') for i in range(5)]

# Add start_day constraints
solver.add(start_days[0] == 1)

for i in range(1, 5):
    prev_city = order[i-1]
    # Compute duration of previous city
    duration_prev = z3.If(prev_city == HAMBURG, 2,
                            z3.If(prev_city == ZURICH, 3,
                            z3.If(prev_city == HEL, 2,
                            z3.If(prev_city == BUCHAREST, 2, 7))))
    solver.add(start_days[i] == start_days[i-1] + duration_prev - 1)

# Add end_day constraint for last city
last_city = order[4]
duration_last = z3.If(last_city == HAMBURG, 2,
                        z3.If(last_city == ZURICH, 3,
                        z3.If(last_city == HEL, 2,
                        z3.If(last_city == BUCHAREST, 2, 7))))
solver.add(start_days[4] + duration_last - 1 == 12)

# Add allowed transitions between consecutive cities
for i in range(4):
    current = order[i]
    next_city = order[i+1]
    # Check if (current, next_city) is in allowed_pairs
    allowed = []
    for a, b in allowed_pairs:
        allowed.append(z3.And(current == a, next_city == b))
    solver.add(z3.Or(allowed))

# Add constraints for Zurich's start day and Split's start day
for i in range(5):
    # Zurich's start day must be <=3
    solver.add(z3.Implies(order[i] == ZURICH, start_days[i] <= 3))
    # Split's start day must be 4
    solver.add(z3.Implies(order[i] == SPLIT, start_days[i] == 4))

# Check if the solver can find a solution
if solver.check() == z3.sat:
    model = solver.model()
    # Extract order and start_days
    order_values = [model.evaluate(order[i]).as_long() for i in range(5)]
    start_values = [model.evaluate(start_days[i]).as_long() for i in range(5)]
    
    # Generate the itinerary
    itinerary = []
    for i in range(5):
        city_code = order_values[i]
        start = start_values[i]
        duration = city_durations[city_code]
        end = start + duration - 1
        city_name = city_names[city_code]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city_name})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")