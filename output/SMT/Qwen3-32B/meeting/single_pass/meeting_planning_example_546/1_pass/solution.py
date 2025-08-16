import z3
import json

# Define friends data
friends_data = [
    {
        'name': 'Nancy',
        'location': 'Pacific Heights',
        'available_start': 480,  # 8:00 AM
        'available_end': 690,    # 11:30 AM
        'required_duration': 90,
    },
    {
        'name': 'Lisa',
        'location': 'Union Square',
        'available_start': 540,  # 9:00 AM
        'available_end': 990,    # 4:30 PM
        'required_duration': 45,
    },
    {
        'name': 'Joshua',
        'location': 'Financial District',
        'available_start': 720,  # 12:00 PM
        'available_end': 915,    # 3:15 PM
        'required_duration': 15,
    },
    {
        'name': 'Kenneth',
        'location': 'Richmond District',
        'available_start': 1275, # 9:15 PM
        'available_end': 1320,   # 10:00 PM
        'required_duration': 30,
    },
    {
        'name': 'Andrew',
        'location': 'Nob Hill',
        'available_start': 690,  # 11:30 AM
        'available_end': 1215,   # 8:15 PM
        'required_duration': 60,
    },
    {
        'name': 'John',
        'location': 'Bayview',
        'available_start': 1005, # 4:45 PM
        'available_end': 1290,   # 9:30 PM
        'required_duration': 75,
    },
]

locations = [
    'Embarcadero',
    'Richmond District',
    'Union Square',
    'Financial District',
    'Pacific Heights',
    'Nob Hill',
    'Bayview',
]

# Precompute friend's location indices
friend_location_indices = [locations.index(f['location']) for f in friends_data]

# Define travel times as a 7x7 matrix
travel_times = [
    # Embarcadero to each location
    [0, 21, 10, 5, 11, 10, 21],
    # Richmond District to each location
    [19, 0, 21, 22, 10, 17, 26],
    # Union Square to each location
    [11, 20, 0, 9, 15, 9, 15],
    # Financial District to each location
    [4, 21, 9, 0, 13, 8, 19],
    # Pacific Heights to each location
    [10, 12, 12, 13, 0, 8, 22],
    # Nob Hill to each location
    [9, 14, 7, 9, 8, 0, 19],
    # Bayview to each location
    [19, 25, 17, 19, 23, 20, 0],
]

# Create Z3 function for travel time
travel_time_func = z3.Function('travel_time', z3.IntSort(), z3.IntSort(), z3.IntSort())
solver = z3.Solver()

# Add constraints for the travel_time_func
for i in range(7):
    for j in range(7):
        solver.add(travel_time_func(i, j) == travel_times[i][j])

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Try for m from 6 down to 1
for m in range(6, 0, -1):
    selected = [z3.Int(f'selected_{i}') for i in range(m)]
    start = [z3.Int(f'start_{i}') for i in range(m)]
    end = [z3.Int(f'end_{i}') for i in range(m)]
    
    constraints = []
    
    # Each selected friend is between 0 and 5 (inclusive)
    for i in range(m):
        constraints.append(z3.And(selected[i] >= 0, selected[i] <= 5))
    
    # All selected friends are unique
    for i in range(m):
        for j in range(i+1, m):
            constraints.append(selected[i] != selected[j])
    
    for i in range(m):
        selected_friend = selected[i]
        
        # Compute available_start_i
        available_start_i = friends_data[5]['available_start']
        for k in range(5, -1, -1):
            available_start_i = z3.If(selected_friend == k, friends_data[k]['available_start'], available_start_i)
        
        # Compute available_end_i
        available_end_i = friends_data[5]['available_end']
        for k in range(5, -1, -1):
            available_end_i = z3.If(selected_friend == k, friends_data[k]['available_end'], available_end_i)
        
        # Compute required_duration_i
        required_duration_i = friends_data[5]['required_duration']
        for k in range(5, -1, -1):
            required_duration_i = z3.If(selected_friend == k, friends_data[k]['required_duration'], required_duration_i)
        
        # Compute loc_idx_i
        loc_idx_i = friend_location_indices[5]
        for k in range(5, -1, -1):
            loc_idx_i = z3.If(selected_friend == k, friend_location_indices[k], loc_idx_i)
        
        # Add constraints for start and end times
        constraints.append(start[i] >= available_start_i)
        constraints.append(end[i] == start[i] + required_duration_i)
        constraints.append(end[i] <= available_end_i)
        
        # Add constraint for arrival time
        if i == 0:
            # arrival_time = 540 + travel_time_func(0, loc_idx_i)
            arrival_time = 540 + travel_time_func(0, loc_idx_i)
            constraints.append(start[i] >= arrival_time)
        else:
            # previous friend's loc_idx
            selected_prev = selected[i-1]
            loc_idx_prev = friend_location_indices[5]
            for k in range(5, -1, -1):
                loc_idx_prev = z3.If(selected_prev == k, friend_location_indices[k], loc_idx_prev)
            # travel_time_prev_to_current = travel_time_func(loc_idx_prev, loc_idx_i)
            travel_time_prev_to_current = travel_time_func(loc_idx_prev, loc_idx_i)
            constraints.append(start[i] >= end[i-1] + travel_time_prev_to_current)
    
    # Add all constraints to the solver
    solver.push()
    solver.add(constraints)
    
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        for i in range(m):
            friend_idx = model.eval(selected[i]).as_long()
            friend = friends_data[friend_idx]
            start_time = model.eval(start[i]).as_long()
            end_time = model.eval(end[i]).as_long()
            start_str = to_time_str(start_time)
            end_str = to_time_str(end_time)
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": start_str,
                "end_time": end_str,
            })
        print("SOLUTION:")
        print(json.dumps({"itinerary": itinerary}))
        exit()
    else:
        solver.pop()

print("No solution found.")