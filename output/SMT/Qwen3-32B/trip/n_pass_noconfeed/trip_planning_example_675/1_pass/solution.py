from z3 import *
import json

# Define cities and their durations
cities_list = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
City, cities_enum = EnumSort('City', cities_list)
dubrovnik = cities_enum[0]
split = cities_enum[1]
milan = cities_enum[2]
porto = cities_enum[3]
krakow = cities_enum[4]
munich = cities_enum[5]

order = [Const(f'order_{i}', City) for i in range(6)]
solver = Solver()

# All cities in order are distinct
solver.add(Distinct(order))

# Durations for each city
durations = {
    dubrovnik: 4,
    split: 3,
    milan: 3,
    porto: 4,
    krakow: 2,
    munich: 5
}

# Start days for each city in the order
start_day = [Int(f'start_day_{i}') for i in range(6)]
solver.add(start_day[0] == 1)

for i in range(1, 6):
    prev_city = order[i-1]
    duration_prev = durations[prev_city]
    solver.add(start_day[i] == start_day[i-1] + duration_prev)

# Constraints for specific cities
# Milan must start on day 11
milan_constraints = []
for i in range(6):
    milan_constraints.append(And(order[i] == milan, start_day[i] == 11))
solver.add(Or(milan_constraints))

# Krakow must start on day 8
krakow_constraints = []
for i in range(6):
    krakow_constraints.append(And(order[i] == krakow, start_day[i] == 8))
solver.add(Or(krakow_constraints))

# Munich must start on day 4
munich_constraints = []
for i in range(6):
    munich_constraints.append(And(order[i] == munich, start_day[i] == 4))
solver.add(Or(munich_constraints))

# Allowed direct flights (bidirectional)
allowed_flights = [
    (munich, porto), (porto, munich),
    (split, milan), (milan, split),
    (milan, porto), (porto, milan),
    (munich, krakow), (krakow, munich),
    (munich, milan), (milan, munich),
    (dubrovnik, munich), (munich, dubrovnik),
    (krakow, split), (split, krakow),
    (krakow, milan), (milan, krakow),
    (munich, split), (split, munich)
]

# Ensure transitions between consecutive cities are direct flights
for i in range(5):
    current = order[i]
    next_c = order[i+1]
    transitions = []
    for a, b in allowed_flights:
        transitions.append(And(current == a, next_c == b))
    solver.add(Or(transitions))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    order_values = [model[order[i]] for i in range(6)]
    start_day_values = [model.evaluate(start_day[i]) for i in range(6)]
    
    # Build itinerary
    itinerary = []
    for i in range(6):
        city_name = order_values[i].decl().name()
        start = start_day_values[i]
        duration = durations[order_values[i]]
        end = start + duration - 1
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city_name})
    
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")