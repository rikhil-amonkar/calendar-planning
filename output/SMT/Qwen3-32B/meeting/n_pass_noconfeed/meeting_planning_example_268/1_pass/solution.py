import json
from z3 import *

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define friends' data
friends = [
    {
        'name': 'Timothy',
        'location': 'Alamo Square',
        'available_start': 720,  # 12:00 PM
        'available_end': 975,    # 4:15 PM
        'min_duration': 105
    },
    {
        'name': 'Joseph',
        'location': 'Russian Hill',
        'available_start': 1005, # 4:45 PM
        'available_end': 1290,   # 9:30 PM
        'min_duration': 60
    },
    {
        'name': 'Mark',
        'location': 'Presidio',
        'available_start': 1125, # 6:45 PM
        'available_end': 1260,   # 9:00 PM
        'min_duration': 60
    }
]

# Z3 variables
solver = Solver()

order0 = Int('order0')
order1 = Int('order1')
order2 = Int('order2')

# Constraints for order variables
solver.add(Distinct(order0, order1, order2))
solver.add(And(0 <= order0, order0 <= 2))
solver.add(And(0 <= order1, order1 <= 2))
solver.add(And(0 <= order2, order2 <= 2))

# Variables for start and end times of each step
start0 = Int('start0')
end0 = Int('end0')
start1 = Int('start1')
end1 = Int('end1')
start2 = Int('start2')
end2 = Int('end2')

# Step 0 constraints
travel_time_0 = If(order0 == 0, 10, If(order0 == 1, 19, 11))
available_start_0 = If(order0 == 0, 720, If(order0 == 1, 1005, 1125))
available_end_0 = If(order0 == 0, 975, If(order0 == 1, 1290, 1260))
min_duration_0 = If(order0 == 0, 105, If(order0 == 1, 60, 60))

solver.add(start0 >= 540 + travel_time_0)
solver.add(start0 >= available_start_0)
solver.add(end0 - start0 >= min_duration_0)
solver.add(end0 <= available_end_0)

# Step 1 constraints
travel_time_1 = If(order0 == 0, 
    If(order1 == 0, 0, If(order1 == 1, 13, 18)),
    If(order0 == 1, 
        If(order1 == 0, 15, If(order1 == 1, 0, 14)),
        # order0 == 2
        If(order1 == 0, 18, If(order1 == 1, 14, 0))
    )
)
available_start_1 = If(order1 == 0, 720, If(order1 == 1, 1005, 1125))
available_end_1 = If(order1 == 0, 975, If(order1 == 1, 1290, 1260))
min_duration_1 = If(order1 == 0, 105, If(order1 == 1, 60, 60))

solver.add(start1 >= end0 + travel_time_1)
solver.add(start1 >= available_start_1)
solver.add(end1 - start1 >= min_duration_1)
solver.add(end1 <= available_end_1)

# Step 2 constraints
travel_time_2 = If(order1 == 0, 
    If(order2 == 0, 0, If(order2 == 1, 13, 18)),
    If(order1 == 1, 
        If(order2 == 0, 15, If(order2 == 1, 0, 14)),
        # order1 == 2
        If(order2 == 0, 18, If(order2 == 1, 14, 0))
    )
)
available_start_2 = If(order2 == 0, 720, If(order2 == 1, 1005, 1125))
available_end_2 = If(order2 == 0, 975, If(order2 == 1, 1290, 1260))
min_duration_2 = If(order2 == 0, 105, If(order2 == 1, 60, 60))

solver.add(start2 >= end1 + travel_time_2)
solver.add(start2 >= available_start_2)
solver.add(end2 - start2 >= min_duration_2)
solver.add(end2 <= available_end_2)

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Extract values
    order0_val = model[order0].as_long()
    order1_val = model[order1].as_long()
    order2_val = model[order2].as_long()
    
    start0_val = model[start0].as_long()
    end0_val = model[end0].as_long()
    start1_val = model[start1].as_long()
    end1_val = model[end1].as_long()
    start2_val = model[start2].as_long()
    end2_val = model[end2].as_long()
    
    # Build the itinerary
    itinerary = []
    for i, order_val in enumerate([order0_val, order1_val, order2_val]):
        friend = friends[order_val]
        if i == 0:
            start = start0_val
            end = end0_val
        elif i == 1:
            start = start1_val
            end = end1_val
        else:
            start = start2_val
            end = end2_val
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": format_time(start),
            "end_time": format_time(end)
        })
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")