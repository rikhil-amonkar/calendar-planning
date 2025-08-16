from z3 import *

# Define the cities and their durations
durations = [4, 3, 4, 5, 5, 2, 5, 4]  # index 0-7: Vienna, Lyon, Edinburgh, Reykjavik, Stuttgart, Manchester, Split, Prague

# Allowed flight pairs (a, b)
allowed_pairs = [
    (3,4), (4,3),
    (4,6), (6,4),
    (4,0), (0,4),
    (7,5), (5,7),
    (2,7), (7,2),
    (5,6), (6,5),
    (7,0), (0,7),
    (0,5), (5,0),
    (7,6), (6,7),
    (0,1), (1,0),
    (4,2), (2,4),
    (6,1), (1,6),
    (4,5), (5,4),
    (7,1), (1,7),
    (3,0), (0,3),
    (7,3), (3,7),
    (0,6), (6,0)
]

# Create solver
s = Solver()

# Create variables for order: order[0] ... order[7]
order = [Int(f'order_{i}') for i in range(8)]

# All order variables are between 0 and 7, and distinct
s.add([And(0 <= order[i], order[i] <= 7) for i in range(8)])
s.add(Distinct(order))

# Create variables for start_days
start_days = [Int(f'start_day_{i}') for i in range(8)]

# Constraints for start_days
s.add(start_days[0] == 1)
for i in range(1, 8):
    prev_city = order[i-1]
    duration_prev = durations[prev_city]
    s.add(start_days[i] == start_days[i-1] + duration_prev - 1)

# Constraints for consecutive flights
for i in range(7):
    current = order[i]
    next_city = order[i+1]
    # Check if (current, next_city) is in allowed_pairs
    constraints = []
    for a, b in allowed_pairs:
        constraints.append(And(current == a, next_city == b))
    s.add(Or(constraints))

# Constraints for Edinburgh (index 2)
for i in range(8):
    s.add(Implies(order[i] == 2, start_days[i] == 5))

# Constraints for Split (index 6)
for i in range(8):
    s.add(Implies(order[i] == 6, And(start_days[i] >= 15, start_days[i] <= 21)))

# Constraint for end day of last city is 25
last_city = order[7]
duration_last = durations[last_city]
s.add(start_days[7] + duration_last - 1 == 25)

# Now, check if the solver can find a solution
if s.check() == sat:
    m = s.model()
    # Extract order and start_days
    order_vals = [m.eval(order[i]).as_long() for i in range(8)]
    start_days_vals = [m.eval(start_days[i]).as_long() for i in range(8)]
    
    # Map order_vals to city names and compute the itinerary
    city_names = {
        0: 'Vienna',
        1: 'Lyon',
        2: 'Edinburgh',
        3: 'Reykjavik',
        4: 'Stuttgart',
        5: 'Manchester',
        6: 'Split',
        7: 'Prague'
    }
    
    # Initialize itinerary
    itinerary = {}
    for i in range(8):
        city_idx = order_vals[i]
        city_name = city_names[city_idx]
        duration = durations[city_idx]
        start = start_days_vals[i]
        end = start + duration - 1
        for day in range(start, end + 1):
            itinerary[day] = city_name
    
    # Create the JSON output
    json_output = {"itinerary": [{"day": day, "city": city} for day, city in sorted(itinerary.items())]}
    print(json.dumps(json_output, indent=2))
else:
    print("No solution found.")