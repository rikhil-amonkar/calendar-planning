from z3 import *
import json

# Define the cities as an EnumSort
City, (Amsterdam, Vienna, Santorini, Lyon) = EnumSort('City', ['Amsterdam', 'Vienna', 'Santorini', 'Lyon'])

# Define the order of cities (symbolic variables)
order = [Const(f'pos_{i}', City) for i in range(4)]

# Ensure all cities are visited once
s = Solver()
s.add(Distinct(order))

# Define allowed transitions
allowed_transitions = [
    (Vienna, Lyon),
    (Vienna, Santorini),
    (Vienna, Amsterdam),
    (Amsterdam, Santorini),
    (Amsterdam, Vienna),
    (Amsterdam, Lyon),
    (Lyon, Vienna),
    (Lyon, Amsterdam),
    (Santorini, Vienna),
    (Santorini, Amsterdam),
]

# Add transition constraints
for i in range(3):
    prev_city = order[i]
    next_city = order[i+1]
    constraints = []
    for a, b in allowed_transitions:
        constraints.append(And(prev_city == a, next_city == b))
    s.add(Or(*constraints))

# Define start and end day variables
start_days = [Int(f'start_{i}') for i in range(4)]
end_days = [Int(f'end_{i}') for i in range(4)]

# First city starts on day 1
s.add(start_days[0] == 1)

# Create duration expressions for each city in the itinerary
duration_exprs = []
for city_var in order:
    expr = If(city_var == Amsterdam, 3,
              If(city_var == Vienna, 7,
                 If(city_var == Santorini, 4, 3)))
    duration_exprs.append(expr)

# Calculate end day for first city
s.add(end_days[0] == start_days[0] + duration_exprs[0] - 1)

# Calculate start and end days for subsequent cities
for i in range(1, 4):
    s.add(start_days[i] == end_days[i-1])
    s.add(end_days[i] == start_days[i] + duration_exprs[i] - 1)

# Ensure the trip ends on day 14
s.add(end_days[3] == 14)

# Event overlap constraints
for i in range(4):
    is_lyon = (order[i] == Lyon)
    s.add(Implies(is_lyon, And(start_days[i] <= 9, end_days[i] >= 7)))

    is_amsterdam = (order[i] == Amsterdam)
    s.add(Implies(is_amsterdam, And(start_days[i] <= 11, end_days[i] >= 9)))

# Check for a satisfying assignment
if s.check() == sat:
    model = s.model()
    city_order = [model[order[i]].as_string() for i in range(4)]
    start_values = [model[start_days[i]].as_long() for i in range(4)]
    end_values = [model[end_days[i]].as_long() for i in range(4)]

    itinerary = []
    for i in range(4):
        city = city_order[i]
        start = start_values[i]
        end = end_values[i]
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})

    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))