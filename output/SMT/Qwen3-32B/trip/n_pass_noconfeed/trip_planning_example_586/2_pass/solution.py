import json
from z3 import *

# Define order variables for the 5 cities
o0, o1, o2, o3, o4 = Ints('o0 o1 o2 o3 o4')
order = [o0, o1, o2, o3, o4]

# Allowed direct flights between cities (as city indices)
allowed_flights = [
    (0, 1), (1, 0),  # Prague and Lyon
    (0, 2), (2, 0),  # Prague and Frankfurt
    (2, 1), (1, 2),  # Frankfurt and Lyon
    (3, 4), (4, 3),  # Helsinki and Naples
    (3, 2), (2, 3),  # Helsinki and Frankfurt
    (4, 2), (2, 4),  # Naples and Frankfurt
    (0, 3), (3, 0)   # Prague and Helsinki
]

# Create Z3 solver instance
solver = Solver()

# Constraint: All cities must be unique (each city is visited once)
solver.add(Distinct(order))

# Constraint: First city is Prague (0)
solver.add(o0 == 0)

# Constraint: Second city is Helsinki (3) to attend the show from day 2 to day 5
solver.add(o1 == 3)

# Constraint: All consecutive city transitions must be via direct flights
for i in range(4):
    a, b = order[i], order[i+1]
    constraints = []
    for x, y in allowed_flights:
        constraints.append(And(a == x, b == y))
    solver.add(Or(constraints))

# Define city durations
durations = {0: 2, 1: 3, 2: 3, 3: 4, 4: 4}

# Helper function to get duration based on city index
def get_duration(city_var):
    return If(city_var == 0, 2,
              If(city_var == 1, 3,
                 If(city_var == 2, 3,
                    If(city_var == 3, 4,
                       If(city_var == 4, 4, 0)))))

# Calculate end days for each city in the sequence
# Start day of first city is 1, and total trip must end on day 12
e0 = durations[0]  # First city is Prague (0), duration 2
e1 = e0 + durations[3] - 1  # Second city is Helsinki (3), duration 4
d2 = get_duration(order[2])
e2 = e1 + d2 - 1
d3 = get_duration(order[3])
e3 = e2 + d3 - 1
d4 = get_duration(order[4])
e4 = e3 + d4 - 1

# Constraint: The trip must end on day 12
solver.add(e4 == 12)

# Solve the constraints
if solver.check() == sat:
    model = solver.model()
    sequence = [model.eval(order[i]).as_long() for i in range(5)]
    city_names = {0: 'Prague', 1: 'Lyon', 2: 'Frankfurt', 3: 'Helsinki', 4: 'Naples'}
    itinerary = []
    current_day = 1
    for i in range(5):
        city_code = sequence[i]
        city_name = city_names[city_code]
        duration = durations[city_code]
        end_day = current_day + duration - 1
        day_range = f"Day {current_day}-{end_day}"
        itinerary.append({'day_range': day_range, 'place': city_name})
        current_day = end_day  # Next city starts on the end day of the current city
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")