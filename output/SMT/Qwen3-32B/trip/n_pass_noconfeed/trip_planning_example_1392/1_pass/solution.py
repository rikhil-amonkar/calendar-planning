import z3
import json

# Define cities and their durations
city_names = ['Barcelona', 'Venice', 'Nice', 'Naples', 'Valencia', 'Stuttgart', 'Split', 'Amsterdam', 'Porto']
durations = [2, 5, 2, 3, 5, 2, 5, 4, 4]  # in the same order as city_names

city_to_idx = {city: idx for idx, city in enumerate(city_names)}

# Define direct flights as pairs of city names, then convert to indices
direct_flights_pairs_names = [
    ('Venice', 'Nice'),
    ('Naples', 'Amsterdam'),
    ('Barcelona', 'Nice'),
    ('Amsterdam', 'Nice'),
    ('Stuttgart', 'Valencia'),
    ('Stuttgart', 'Porto'),
    ('Split', 'Stuttgart'),
    ('Split', 'Naples'),
    ('Valencia', 'Amsterdam'),
    ('Barcelona', 'Porto'),
    ('Valencia', 'Naples'),
    ('Venice', 'Amsterdam'),
    ('Barcelona', 'Naples'),
    ('Barcelona', 'Valencia'),
    ('Split', 'Amsterdam'),
    ('Barcelona', 'Venice'),
    ('Stuttgart', 'Amsterdam'),
    ('Naples', 'Nice'),
    ('Venice', 'Stuttgart'),
    ('Split', 'Barcelona'),
    ('Porto', 'Nice'),
    ('Barcelona', 'Stuttgart'),
    ('Venice', 'Naples'),
    ('Porto', 'Amsterdam'),
    ('Porto', 'Valencia'),
    ('Stuttgart', 'Naples'),
    ('Barcelona', 'Amsterdam'),
]

# Add reverse of each pair
direct_flights_pairs_names_reversed = []
for a, b in direct_flights_pairs_names:
    direct_flights_pairs_names_reversed.append((a, b))
    direct_flights_pairs_names_reversed.append((b, a))

direct_flights_pairs = [(city_to_idx[a], city_to_idx[b]) for a, b in direct_flights_pairs_names_reversed]

# Create Z3 solver
solver = z3.Solver()

# Create variables for the sequence of cities
seq = [z3.Int(f'seq_{i}') for i in range(9)]

# Constraints: each city is used exactly once (permutation)
solver.add(z3.Distinct(seq))
for i in range(9):
    solver.add(seq[i] >= 0, seq[i] <= 8)

# Create variables for start_day of each city in the sequence
start_day = [z3.Int(f'start_day_{i}') for i in range(9)]

# Constraint for start_day[0]
solver.add(start_day[0] == 1)

# Function to get duration based on city index
def get_duration_expr(x):
    return z3.If(x == 0, 2,
        z3.If(x == 1, 5,
            z3.If(x == 2, 2,
                z3.If(x == 3, 3,
                    z3.If(x == 4, 5,
                        z3.If(x == 5, 2,
                            z3.If(x == 6, 5,
                                z3.If(x == 7, 4, 4)))))))
    )

# Constraints for start_day[i] for i >= 1
for i in range(1, 9):
    prev_city = seq[i-1]
    duration_prev = get_duration_expr(prev_city)
    solver.add(start_day[i] == start_day[i-1] + duration_prev - 1)

# Constraints for fixed cities
# Barcelona (index 0) must start on day 5
for i in range(9):
    solver.add(z3.Implies(seq[i] == 0, start_day[i] == 5))

# Venice (index 1) must start on day 6
for i in range(9):
    solver.add(z3.Implies(seq[i] == 1, start_day[i] == 6))

# Nice (index 2) must start on day 23
for i in range(9):
    solver.add(z3.Implies(seq[i] == 2, start_day[i] == 23))

# Naples (index 3) must have start_day between 16 and 20
for i in range(9):
    solver.add(z3.Implies(seq[i] == 3, z3.And(start_day[i] >= 16, start_day[i] <= 20)))

# Constraints for transitions between consecutive cities
for i in range(8):
    current_city = seq[i]
    next_city = seq[i+1]
    # Create a big OR of all allowed transitions
    allowed = []
    for a, b in direct_flights_pairs:
        allowed.append(z3.And(current_city == a, next_city == b))
    solver.add(z3.Or(allowed))

# Check if the solver can find a solution
if solver.check() == z3.sat:
    model = solver.model()
    # Extract the sequence
    sequence = [model.evaluate(seq[i]).as_long() for i in range(9)]
    # Extract start_days
    start_days = [model.evaluate(start_day[i]).as_long() for i in range(9)]
    # Generate the itinerary
    itinerary = []
    for i in range(9):
        city_idx = sequence[i]
        city_name = city_names[city_idx]
        duration = durations[city_idx]
        start = start_days[i]
        end = start + duration - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city_name
        })
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")