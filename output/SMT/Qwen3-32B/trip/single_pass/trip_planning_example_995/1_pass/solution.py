from z3 import *

# Define the cities after Barcelona: Br (0), C (1), O (2), S (3), St (4), V (5)
# Direct flights between these cities are defined by the allowed_pairs list.

# Create solver
solver = Solver()

# Define the order variables
order = [Int(f'order_{i}') for i in range(6)]
for i in range(6):
    solver.add(And(order[i] >= 0, order[i] <= 5))
solver.add(Distinct(order))

# Define start_days for each city in the order
start_days = [Int(f'start_{i}') for i in range(6)]
solver.add(start_days[0] == 3)  # First city starts on day 3 (after B's 3 days)

# Define durations for each city
def get_duration(city_id):
    return If(city_id == 0, 3,  # Br
              If(city_id == 1, 3,  # C
                 If(city_id == 2, 2,  # O
                    If(city_id == 3, 4,  # S
                       If(city_id == 4, 3,  # St
                          If(city_id == 5, 4,  # V
                             0)))))  # default 0 (should not happen)

# Compute start_days for i >=1
for i in range(1, 6):
    prev_city = order[i-1]
    duration_prev = get_duration(prev_city)
    solver.add(start_days[i] == start_days[i-1] + duration_prev)

# Constraint: end day of last city is 16
last_city = order[5]
duration_last = get_duration(last_city)
end_day_last = start_days[5] + duration_last - 1
solver.add(end_day_last == 16)

# Constraints for Oslo and Brussels
for i in range(6):
    # Oslo (2) must have start between 2 and 4
    solver.add(Implies(order[i] == 2, And(start_days[i] >= 2, start_days[i] <= 4)))
    # Brussels (0) must have start between 7 and 11
    solver.add(Implies(order[i] == 0, And(start_days[i] >= 7, start_days[i] <= 11)))

# Allowed pairs between cities after B
allowed_pairs = [
    (0,5), (0,2), (1,0), (1,5), (1,4), (1,3), 
    (2,0), (2,1), (2,3), (2,5), (3,1), (3,4), 
    (4,5), (4,3), (5,0), (5,2), (5,4)
]

# Add constraints for consecutive flights
for i in range(5):  # i from 0 to 4
    current = order[i]
    next_c = order[i+1]
    # Create a condition that (current, next_c) is in allowed_pairs
    conditions = []
    for (c, n) in allowed_pairs:
        conditions.append(And(current == c, next_c == n))
    solver.add(Or(conditions))

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    # Extract the order and start_days
    order_vals = [model.eval(order[i]).as_long() for i in range(6)]
    start_days_vals = [model.eval(start_days[i]).as_long() for i in range(6)]
    
    # Now build the itinerary
    # Cities are: 0=Brussels, 1=Copenhagen, 2=Oslo, 3=Split, 4=Stuttgart, 5=Venice
    city_names = {0: 'Brussels', 1: 'Copenhagen', 2: 'Oslo', 3: 'Split', 4: 'Stuttgart', 5: 'Venice'}
    # The itinerary starts with Barcelona (days 1-3)
    itinerary = []
    for day in range(1, 4):
        itinerary.append({'day': day, 'city': 'Barcelona'})
    
    # Now process the order
    for i in range(6):
        city_id = order_vals[i]
        city_name = city_names[city_id]
        start_day = start_days_vals[i]
        duration = {0:3, 1:3, 2:2, 3:4, 4:3, 5:4}[city_id]
        end_day = start_day + duration - 1
        for day in range(start_day, end_day + 1):
            itinerary.append({'day': day, 'city': city_name})
    
    # Now sort the itinerary by day and check for duplicates
    itinerary.sort(key=lambda x: x['day'])
    # Now output as JSON
    import json
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print("No solution found.")