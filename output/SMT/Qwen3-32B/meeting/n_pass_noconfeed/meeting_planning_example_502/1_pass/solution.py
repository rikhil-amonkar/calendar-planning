from z3 import *
import json

# Define friends' data
friends_data = [
    {'name': 'Stephanie', 'location': 1, 'available_start': 660, 'available_end': 900, 'required': 105},
    {'name': 'Karen', 'location': 2, 'available_start': 825, 'available_end': 990, 'required': 15},
    {'name': 'Brian', 'location': 3, 'available_start': 900, 'available_end': 1035, 'required': 30},
    {'name': 'Rebecca', 'location': 4, 'available_start': 480, 'available_end': 675, 'required': 30},
    {'name': 'Joseph', 'location': 5, 'available_start': 495, 'available_end': 570, 'required': 60},
    {'name': 'Steven', 'location': 6, 'available_start': 870, 'available_end': 1245, 'required': 120}
]

# Travel time matrix between locations (0: Financial District, 1: Golden Gate Park, ..., 6: North Beach)
travel_time_matrix = [
    [0, 23, 5, 9, 10, 13, 7],  # Financial District
    [26, 0, 23, 22, 24, 16, 24],  # Golden Gate Park
    [5, 23, 0, 7, 8, 10, 3],  # Chinatown
    [9, 22, 7, 0, 15, 15, 10],  # Union Square
    [11, 25, 12, 13, 0, 12, 6],  # Fisherman's Wharf
    [13, 15, 11, 12, 13, 0, 8],  # Pacific Heights
    [8, 22, 6, 7, 5, 8, 0]  # North Beach
]

# Mapping from friend index to their location index in the travel_time_matrix
friend_to_location = [1, 2, 3, 4, 5, 6]  # Stephanie, Karen, Brian, Rebecca, Joseph, Steven

solver = Optimize()

# Variables for inclusion and times
is_included = [Bool(f"is_included_{i}") for i in range(6)]
start_time = [Int(f"start_time_{i}") for i in range(6)]
end_time = [Int(f"end_time_{i}") for i in range(6)]

# Objective: maximize number of included friends
objective = Sum([If(is_included[i], 1, 0) for i in range(6)])
solver.maximize(objective)

# Add constraints for each friend's inclusion
for i in range(6):
    # If included, start and end times must satisfy availability and duration
    solver.add(Implies(is_included[i], 
                       And(start_time[i] >= friends_data[i]['available_start'],
                           end_time[i] <= friends_data[i]['available_end'],
                           end_time[i] - start_time[i] >= friends_data[i]['required'])))
    # Also, start_time must be after arrival at their location
    location_i = friend_to_location[i]
    travel_time_fd = travel_time_matrix[0][location_i]  # 0 is Financial District
    solver.add(Implies(is_included[i], start_time[i] >= 540 + travel_time_fd))

# Add pairwise constraints between friends
for i in range(6):
    for j in range(i+1, 6):
        # Get travel times between i and j, and j and i
        loc_i = friend_to_location[i]
        loc_j = friend_to_location[j]
        travel_time_i_to_j = travel_time_matrix[loc_i][loc_j]
        travel_time_j_to_i = travel_time_matrix[loc_j][loc_i]
        # If both are included, then either i comes before j or j comes before i
        constraint = Implies(And(is_included[i], is_included[j]),
                             Or(start_time[i] + (end_time[i] - start_time[i]) + travel_time_i_to_j <= start_time[j],
                                start_time[j] + (end_time[j] - start_time[j]) + travel_time_j_to_i <= start_time[i]))
        solver.add(constraint)

# Check if the solver can find a solution
result = solver.check()
if result == sat:
    model = solver.model()
    # Extract included friends
    included = []
    for i in range(6):
        if is_included[i].as_string() in model:
            if model.eval(is_included[i]):
                included.append(i)
    # Now, sort the included friends based on their start times to get the itinerary order
    included_sorted = sorted(included, key=lambda x: model.eval(start_time[x]).as_long())
    # Build the itinerary
    itinerary = []
    for idx in included_sorted:
        name = friends_data[idx]['name']
        loc = ['Financial District', 'Golden Gate Park', 'Chinatown', 'Union Square', 'Fisherman\'s Wharf', 'Pacific Heights', 'North Beach'][friend_to_location[idx]]
        start = model.eval(start_time[idx]).as_long()
        end = model.eval(end_time[idx]).as_long()
        # Convert to H:MM format
        def to_time_str(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": to_time_str(start),
            "end_time": to_time_str(end)
        })
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"itinerary": []}, indent=2))