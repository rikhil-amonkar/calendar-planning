from z3 import *
import json

# Define the cities as an EnumSort
City, (Amsterdam, Vienna, Santorini, Lyon) = EnumSort('City', ['Amsterdam', 'Vienna', 'Santorini', 'Lyon'])

# Durations for each city
durations = {
    Amsterdam: 3,
    Vienna: 7,
    Santorini: 4,
    Lyon: 3
}

# Allowed transitions (direct flights)
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

# Create variables for the order of the cities
order = [Const(f'pos_{i}', City) for i in range(4)]

# All cities must be distinct
s = Solver()
s.add(Distinct(order))

# Add constraints for allowed transitions between consecutive cities
for i in range(3):
    prev_city = order[i]
    next_city = order[i+1]
    constraints = []
    for a, b in allowed_transitions:
        constraints.append(And(prev_city == a, next_city == b))
    s.add(Or(*constraints))

# Create variables for start and end days
start_days = [Int(f'start_{i}') for i in range(4)]
end_days = [Int(f'end_{i}') for i in range(4)]

# First city starts on day 1
s.add(start_days[0] == 1)
# Calculate end day for first city
s.add(end_days[0] == start_days[0] + durations[order[0]] - 1)

# Calculate start and end days for subsequent cities
for i in range(1, 4):
    s.add(start_days[i] == end_days[i-1])
    s.add(end_days[i] == start_days[i] + durations[order[i]] - 1)

# Ensure the last day of the trip is day 14
s.add(end_days[3] == 14)

# Constraints for event overlaps
for i in range(4):
    is_lyon = (order[i] == Lyon)
    s.add(Implies(is_lyon, And(start_days[i] <= 9, end_days[i] >= 7)))
    
    is_amsterdam = (order[i] == Amsterdam)
    s.add(Implies(is_amsterdam, And(start_days[i] <= 11, end_days[i] >= 9)))

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