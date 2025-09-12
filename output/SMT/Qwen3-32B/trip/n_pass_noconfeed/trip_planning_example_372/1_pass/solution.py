import z3
import json

solver = z3.Solver()

# Define the cities sequence (0: Seville, 1: Stuttgart, 2: Porto, 3: Madrid)
seq = [z3.Int(f'seq_{i}') for i in range(4)]
s = [z3.Int(f's_{i}') for i in range(4)]

# Constraints for sequence to be a permutation of [0, 1, 2, 3]
solver.add(z3.Distinct(seq))
for city in seq:
    solver.add(z3.And(0 <= city, city <= 3))

# Stay durations sum to 10
solver.add(sum(s) == 10)
for si in s:
    solver.add(si >= 1)

# Transition constraints
allowed_transitions = [
    (0, 2), (2, 0),  # Seville-Porto
    (2, 1), (1, 2),  # Porto-Stuttgart
    (3, 2), (2, 3),  # Madrid-Porto
    (3, 0), (0, 3),  # Madrid-Seville
]
for i in range(3):
    current = seq[i]
    next_city = seq[i+1]
    constraints = []
    for a, b in allowed_transitions:
        constraints.append(z3.And(current == a, next_city == b))
    solver.add(z3.Or(*constraints))

# Duration constraints
required_duration = {0: 2, 1: 7, 2: 3, 3: 4}
for i in range(4):
    city = seq[i]
    si = s[i]
    in_transitions = 1 if i > 0 else 0
    out_transitions = 1 if i < 3 else 0
    rd = required_duration[city]
    solver.add(si + in_transitions + out_transitions == rd)

# Conference constraints for day 7 and 13
# Day 7
day7_constraints = []
for i in range(4):
    if i == 0:
        ps = 1
        pe = s[0] + 1
    elif i == 1:
        ps = s[0] + 1
        pe = ps + s[1] + 1
    elif i == 2:
        ps = s[0] + s[1] + 2
        pe = ps + s[2] + 1
    else:
        ps = s[0] + s[1] + s[2] + 3
        pe = ps + s[3]
    day7_constraints.append(z3.And(seq[i] == 1, ps <= 7, 7 <= pe))
solver.add(z3.Or(*day7_constraints))

# Day 13
day13_constraints = []
for i in range(4):
    if i == 0:
        ps = 1
        pe = s[0] + 1
    elif i == 1:
        ps = s[0] + 1
        pe = ps + s[1] + 1
    elif i == 2:
        ps = s[0] + s[1] + 2
        pe = ps + s[2] + 1
    else:
        ps = s[0] + s[1] + s[2] + 3
        pe = ps + s[3]
    day13_constraints.append(z3.And(seq[i] == 1, ps <= 13, 13 <= pe))
solver.add(z3.Or(*day13_constraints))

# Relatives visit: some day between 1-4 in Madrid (3)
relatives_constraints = []
for i in range(4):
    for d in range(1, 5):  # days 1-4
        if i == 0:
            ps = 1
            pe = s[0] + 1
        elif i == 1:
            ps = s[0] + 1
            pe = ps + s[1] + 1
        elif i == 2:
            ps = s[0] + s[1] + 2
            pe = ps + s[2] + 1
        else:
            ps = s[0] + s[1] + s[2] + 3
            pe = ps + s[3]
        relatives_constraints.append(z3.And(seq[i] == 3, ps <= d, d <= pe))
solver.add(z3.Or(*relatives_constraints))

# Check if the constraints are satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    # Extract the sequence and stay durations
    seq_vals = [model.evaluate(seq[i]).as_long() for i in range(4)]
    s_vals = [model.evaluate(s[i]).as_long() for i in range(4)]
    # Now, build the itinerary
    # Calculate presence_start and presence_end for each city in the sequence
    presence_start = [0] * 4
    presence_end = [0] * 4
    for i in range(4):
        if i == 0:
            presence_start[i] = 1
            presence_end[i] = s_vals[0] + 1
        elif i == 1:
            presence_start[i] = s_vals[0] + 1
            presence_end[i] = presence_start[i] + s_vals[1] + 1
        elif i == 2:
            presence_start[i] = s_vals[0] + s_vals[1] + 2
            presence_end[i] = presence_start[i] + s_vals[2] + 1
        else:
            presence_start[i] = s_vals[0] + s_vals[1] + s_vals[2] + 3
            presence_end[i] = presence_start[i] + s_vals[3]
    # Build the itinerary list
    itinerary = []
    for i in range(4):
        city_id = seq_vals[i]
        start_day = presence_start[i]
        end_day = presence_end[i]
        city_name = {0: 'Seville', 1: 'Stuttgart', 2: 'Porto', 3: 'Madrid'}[city_id]
        itinerary.append({'day_range': f"Day {start_day}-{end_day}", 'place': city_name})
    # Output as JSON
    print(json.dumps({'itinerary': itinerary}))
else:
    print("No solution found.")