import z3
import json

# Define friends data
friends_data = [
    {
        'name': 'Anthony',
        'location': 'Alamo Square',
        'available_start': 7 * 60 + 45,  # 7:45 AM
        'available_end': 19 * 60 + 45,   # 7:45 PM
        'min_duration': 15
    },
    {
        'name': 'Steven',
        'location': 'Golden Gate Park',
        'available_start': 8 * 60 + 30,  # 8:30 AM
        'available_end': 17 * 60 + 0,    # 5:00 PM
        'min_duration': 75
    },
    {
        'name': 'Sandra',
        'location': 'Pacific Heights',
        'available_start': 14 * 60 + 45, # 2:45 PM
        'available_end': 21 * 60 + 45,   # 9:45 PM
        'min_duration': 45
    },
    {
        'name': 'Kevin',
        'location': "Fisherman's Wharf",
        'available_start': 19 * 60 + 15, # 7:15 PM
        'available_end': 21 * 60 + 45,   # 9:45 PM
        'min_duration': 75
    },
    {
        'name': 'Stephanie',
        'location': 'Russian Hill',
        'available_start': 20 * 60 + 0,  # 8:00 PM
        'available_end': 20 * 60 + 45,   # 8:45 PM
        'min_duration': 15
    }
]

# Precompute travel times between friends and from HA to friends
friends_locations = [f['location'] for f in friends_data]
travel_time = {
    'Haight-Ashbury': {
        'Russian Hill': 17,
        "Fisherman's Wharf": 23,
        'Nob Hill': 15,
        'Golden Gate Park': 7,
        'Alamo Square': 5,
        'Pacific Heights': 12,
    },
    'Russian Hill': {
        'Haight-Ashbury': 17,
        "Fisherman's Wharf": 7,
        'Nob Hill': 5,
        'Golden Gate Park': 21,
        'Alamo Square': 15,
        'Pacific Heights': 7,
    },
    "Fisherman's Wharf": {
        'Haight-Ashbury': 22,
        'Russian Hill': 7,
        'Nob Hill': 11,
        'Golden Gate Park': 25,
        'Alamo Square': 20,
        'Pacific Heights': 12,
    },
    'Nob Hill': {
        'Haight-Ashbury': 13,
        'Russian Hill': 5,
        "Fisherman's Wharf": 11,
        'Golden Gate Park': 17,
        'Alamo Square': 11,
        'Pacific Heights': 8,
    },
    'Golden Gate Park': {
        'Haight-Ashbury': 7,
        'Russian Hill': 21,
        "Fisherman's Wharf": 25,
        'Nob Hill': 17,
        'Alamo Square': 10,
        'Pacific Heights': 16,
    },
    'Alamo Square': {
        'Haight-Ashbury': 5,
        'Russian Hill': 13,
        "Fisherman's Wharf": 19,
        'Nob Hill': 11,
        'Golden Gate Park': 9,
        'Pacific Heights': 10,
    },
    'Pacific Heights': {
        'Haight-Ashbury': 11,
        'Russian Hill': 7,
        "Fisherman's Wharf": 13,
        'Nob Hill': 8,
        'Golden Gate Park': 15,
        'Alamo Square': 10,
    },
}

# Precompute travel time matrix between friends
travel_time_matrix = [[0] * 5 for _ in range(5)]
for k in range(5):
    for m in range(5):
        loc_k = friends_locations[k]
        loc_m = friends_locations[m]
        travel_time_matrix[k][m] = travel_time[loc_k][loc_m]

# Precompute travel time from HA to each friend
ha_to_friend_travel = [travel_time['Haight-Ashbury'][loc] for loc in friends_locations]

def get_travel_time_expr(a, b, matrix):
    expr = 0
    for k in range(5):
        for m in range(5):
            expr = z3.If(z3.And(a == k, b == m), matrix[k][m], expr)
    return expr

# Create Z3 variables
solver = z3.Optimize()

# Define variables for each step
is_used = [z3.Bool(f'step_{i}_used') for i in range(5)]
friend = [z3.Int(f'step_{i}_friend') for i in range(5)]
arrival = [z3.Int(f'step_{i}_arrival') for i in range(5)]
start = [z3.Int(f'step_{i}_start') for i in range(5)]
end = [z3.Int(f'step_{i}_end') for i in range(5)]

# Add constraints for each step
for i in range(5):
    # If step is used, friend is between 0 and 4
    solver.add(z3.Implies(is_used[i], z3.And(friend[i] >= 0, friend[i] <= 4)))

    # Define available_start, available_end, min_duration for the friend
    available_start_expr = z3.If(friend[i] == 0, friends_data[0]['available_start'],
                                 z3.If(friend[i] == 1, friends_data[1]['available_start'],
                                       z3.If(friend[i] == 2, friends_data[2]['available_start'],
                                             z3.If(friend[i] == 3, friends_data[3]['available_start'],
                                                   friends_data[4]['available_start']))))
    available_end_expr = z3.If(friend[i] == 0, friends_data[0]['available_end'],
                               z3.If(friend[i] == 1, friends_data[1]['available_end'],
                                     z3.If(friend[i] == 2, friends_data[2]['available_end'],
                                           z3.If(friend[i] == 3, friends_data[3]['available_end'],
                                                 friends_data[4]['available_end']))))
    min_duration_expr = z3.If(friend[i] == 0, friends_data[0]['min_duration'],
                              z3.If(friend[i] == 1, friends_data[1]['min_duration'],
                                    z3.If(friend[i] == 2, friends_data[2]['min_duration'],
                                          z3.If(friend[i] == 3, friends_data[3]['min_duration'],
                                                friends_data[4]['min_duration']))))

    # Define arrival[i]
    if i == 0:
        ha_to_friend_expr = z3.If(friend[i] == 0, ha_to_friend_travel[0],
                                  z3.If(friend[i] == 1, ha_to_friend_travel[1],
                                        z3.If(friend[i] == 2, ha_to_friend_travel[2],
                                              z3.If(friend[i] == 3, ha_to_friend_travel[3],
                                                    ha_to_friend_travel[4]))))
        arrival_expr = 540 + ha_to_friend_expr
    else:
        prev_friend = friend[i-1]
        curr_friend = friend[i]
        travel_time_expr = get_travel_time_expr(prev_friend, curr_friend, travel_time_matrix)
        arrival_expr = end[i-1] + travel_time_expr

    # Add constraints for arrival, start, end
    solver.add(z3.Implies(is_used[i], arrival[i] == arrival_expr))
    solver.add(z3.Implies(is_used[i], start[i] >= arrival[i]))
    solver.add(z3.Implies(is_used[i], end[i] == start[i] + min_duration_expr))
    solver.add(z3.Implies(is_used[i], start[i] >= available_start_expr))
    solver.add(z3.Implies(is_used[i], end[i] <= available_end_expr))

    # Ensure steps are used in order
    if i > 0:
        solver.add(z3.Implies(is_used[i], is_used[i-1]))

# Ensure each friend is used at most once
for k in range(5):
    count_expr = z3.Sum([z3.If(z3.And(is_used[i], friend[i] == k), 1, 0) for i in range(5)])
    solver.add(count_expr <= 1)

# Objective: maximize the number of used steps
objective = z3.Sum([z3.If(is_used[i], 1, 0) for i in range(5)])
solver.maximize(objective)

# Check if the problem is satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    # Extract the results
    itinerary = []
    for i in range(5):
        if model.eval(is_used[i]).as_string() == 'True':
            k = model.eval(friend[i]).as_long()
            friend_info = friends_data[k]
            start_time = model.eval(start[i]).as_long()
            end_time = model.eval(end[i]).as_long()
            # Convert to H:MM format
            def to_time_str(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours}:{mins:02d}"
            itinerary.append({
                "action": "meet",
                "location": friend_info['location'],
                "person": friend_info['name'],
                "start_time": to_time_str(start_time),
                "end_time": to_time_str(end_time)
            })
    # Output JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))