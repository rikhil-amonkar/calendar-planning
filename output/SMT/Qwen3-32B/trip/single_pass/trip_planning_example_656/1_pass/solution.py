from z3 import *
import json

# Define cities and their durations
cities_list = ['Reykjavik', 'Istanbul', 'Edinburgh', 'Oslo', 'Stuttgart', 'Bucharest']
durations = [5, 4, 5, 2, 3, 5]

# Define allowed flights
allowed_flights_set = {
    ('Reykjavik', 'Stuttgart'),
    ('Stuttgart', 'Reykjavik'),
    ('Reykjavik', 'Bucharest'),
    ('Bucharest', 'Reykjavik'),
    ('Reykjavik', 'Istanbul'),
    ('Istanbul', 'Reykjavik'),
    ('Stuttgart', 'Edinburgh'),
    ('Edinburgh', 'Stuttgart'),
    ('Istanbul', 'Edinburgh'),
    ('Edinburgh', 'Istanbul'),
    ('Istanbul', 'Oslo'),
    ('Oslo', 'Istanbul'),
    ('Bucharest', 'Oslo'),
    ('Oslo', 'Bucharest'),
    ('Istanbul', 'Stuttgart'),
    ('Stuttgart', 'Istanbul'),
    ('Oslo', 'Edinburgh'),
    ('Edinburgh', 'Oslo'),
    ('Oslo', 'Reykjavik'),
    ('Reykjavik', 'Oslo'),
}

# Precompute allowed_pairs as (a, b) where a and b are indices
is_allowed = [[False for _ in range(6)] for _ in range(6)]
for i in range(6):
    for j in range(6):
        if (cities_list[i], cities_list[j]) in allowed_flights_set:
            is_allowed[i][j] = True

allowed_pairs = [(a, b) for a in range(6) for b in range(6) if is_allowed[a][b]]

# Create Z3 solver
solver = Solver()

# Variables for the order of cities (0-5 indices)
order_vars = [Int(f'order_{i}') for i in range(6)]

# Add constraints for order_vars to be a permutation of 0-5
solver.add(Distinct(order_vars))
solver.add(And([And(0 <= order_vars[i], order_vars[i] <= 5) for i in range(6)]))

# Add constraints for allowed flights between consecutive cities
for i in range(5):
    constraints = []
    for a, b in allowed_pairs:
        constraints.append(And(order_vars[i] == a, order_vars[i+1] == b))
    solver.add(Or(constraints))

# Define start day variables for each position
s = [Int(f's_{i}') for i in range(6)]

# Add constraint for the first day
solver.add(s[0] == 1)

# Add constraints for start day calculations
for i in range(5):
    # Create piecewise function for duration at position i
    duration_i = If(order_vars[i] == 0, 5,
           If(order_vars[i] == 1, 4,
           If(order_vars[i] == 2, 5,
           If(order_vars[i] == 3, 2,
           If(order_vars[i] == 4, 3,
           If(order_vars[i] == 5, 5, 0))))))
    solver.add(s[i+1] == s[i] + duration_i - 1)

# Add constraints for Istanbul (index 1) and Oslo (index 3)
ist_index = 1  # 'Istanbul'
osl_index = 3  # 'Oslo'

for i in range(6):
    # Constraints for Istanbul
    solver.add(Implies(order_vars[i] == ist_index, And(s[i] >= 2, s[i] <= 8)))
    # Constraints for Oslo
    solver.add(Implies(order_vars[i] == osl_index, And(s[i] >= 7, s[i] <= 9)))

# Add constraint for the last day to be 19
duration_last = If(order_vars[5] == 0, 5,
           If(order_vars[5] == 1, 4,
           If(order_vars[5] == 2, 5,
           If(order_vars[5] == 3, 2,
           If(order_vars[5] == 4, 3,
           If(order_vars[5] == 5, 5, 0)))))
solver.add(s[5] + duration_last - 1 == 19)

# Check for solution
if solver.check() == sat:
    model = solver.model()
    # Extract order and start day values
    order_val = [model[order_vars[i]].as_long() for i in range(6)]
    s_val = [model[s[i]].as_long() for i in range(6)]
    
    # Build the itinerary
    itinerary = [''] * 19  # 19 days, 0-based index
    current_day = 1
    for i in range(6):
        city_index = order_val[i]
        city = cities_list[city_index]
        duration = durations[city_index]
        end_day = current_day + duration - 1
        for day in range(current_day, end_day + 1):
            itinerary[day - 1] = city
        current_day = end_day  # Next city starts on end_day
    
    # Format the result as required
    result = {'itinerary': [{'day': day + 1, 'city': itinerary[day]} for day in range(19)]}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")