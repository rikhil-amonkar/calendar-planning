from z3 import *
import json

# Define cities as integers
NICE = 0
LYON = 1
DUBLIN = 2
KRAKOW = 3
FRANKFURT = 4

# Duration of stay in each city
durations = [5, 4, 7, 6, 2]  # [Nice, Lyon, Dublin, Krakow, Frankfurt]

# Direct flight connections
direct_flights = {
    (NICE, LYON), (LYON, NICE),
    (NICE, DUBLIN), (DUBLIN, NICE),
    (NICE, FRANKFURT), (FRANKFURT, NICE),
    (LYON, FRANKFURT), (FRANKFURT, LYON),
    (LYON, DUBLIN), (DUBLIN, LYON),
    (DUBLIN, KRAKOW), (KRAKOW, DUBLIN),
    (DUBLIN, FRANKFURT), (FRANKFURT, DUBLIN),
    (KRAKOW, FRANKFURT), (FRANKFURT, KRAKOW),
}

allowed_transitions = list(direct_flights)

# Initialize Z3 solver
solver = Solver()

# Sequence of cities to visit (5 in total)
seq = [Int(f'seq_{i}') for i in range(5)]

# Constraint: All cities are distinct
solver.add(Distinct(seq))

# Constraint: First city is Nice, last is Frankfurt
solver.add(seq[0] == NICE)
solver.add(seq[4] == FRANKFURT)

# Constraint: Consecutive cities must be connected by direct flight
for i in range(4):
    constraints = []
    for x, y in allowed_transitions:
        constraints.append(And(seq[i] == x, seq[i+1] == y))
    solver.add(Or(constraints))

# Start day variables
start_days = [Int(f'start_day_{i}') for i in range(5)]
solver.add(start_days[0] == 1)

# Compute start days based on durations
for i in range(4):
    duration_i = If(seq[i] == NICE, 5,
                    If(seq[i] == LYON, 4,
                       If(seq[i] == DUBLIN, 7,
                          If(seq[i] == KRAKOW, 6, 2))))
    d_json_i = duration_i - 1
    solver.add(start_days[i+1] == start_days[i] + d_json_i)

# Constraint: Last city starts on day 19
solver.add(start_days[4] == 19)

# Solve the model
if solver.check() == sat:
    model = solver.model()
    sequence = [model.evaluate(seq[i]).as_long() for i in range(5)]
    start_days_values = [model.evaluate(start_days[i]).as_long() for i in range(5)]

    # Map city IDs to names
    city_names = {0: "Nice", 1: "Lyon", 2: "Dublin", 3: "Krakow", 4: "Frankfurt"}

    # Generate itinerary
    itinerary = []
    for i in range(5):
        current_city = sequence[i]
        if i < 4:
            end_day = start_days_values[i+1] - 1
        else:
            end_day = start_days_values[i] + durations[current_city] - 1
        for day in range(start_days_values[i], end_day + 1):
            itinerary.append({"day": day, "city": city_names[current_city]})

    # Output JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")