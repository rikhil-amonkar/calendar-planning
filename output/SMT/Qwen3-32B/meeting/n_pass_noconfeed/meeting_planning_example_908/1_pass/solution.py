from z3 import *
import json

def convert_minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define friends
friends = [
    {
        'name': 'Mark',
        'location': 1,  # Fisherman's Wharf
        'available_start': 495,  # 8:15 AM
        'available_end': 600,  # 10:00 AM
        'duration': 30
    },
    {
        'name': 'Stephanie',
        'location': 2,  # Presidio
        'available_start': 735,  # 12:15 PM
        'available_end': 900,  # 3:00 PM
        'duration': 75
    },
    {
        'name': 'Betty',
        'location': 3,  # Bayview
        'available_start': 435,  # 7:15 AM
        'available_end': 1230,  # 8:30 PM
        'duration': 15
    },
    {
        'name': 'Brian',
        'location': 6,  # The Castro
        'available_start': 555,  # 9:15 AM
        'available_end': 795,  # 1:15 PM
        'duration': 30
    },
    {
        'name': 'Joseph',
        'location': 7,  # Marina District
        'available_start': 645,  # 10:45 AM
        'available_end': 900,  # 3:00 PM
        'duration': 90
    },
    {
        'name': 'Ashley',
        'location': 8,  # Richmond District
        'available_start': 585,  # 9:45 AM
        'available_end': 675,  # 11:15 AM
        'duration': 45
    },
    {
        'name': 'Patricia',
        'location': 9,  # Union Square
        'available_start': 990,  # 4:30 PM
        'available_end': 1200,  # 8:00 PM
        'duration': 120
    },
    {
        'name': 'Lisa',
        'location': 4,  # Haight-Ashbury
        'available_start': 930,  # 3:30 PM
        'available_end': 1110,  # 6:30 PM
        'duration': 45
    },
    {
        'name': 'William',
        'location': 5,  # Russian Hill
        'available_start': 1125,  # 6:45 PM
        'available_end': 1200,  # 8:00 PM
        'duration': 60
    },
    {
        'name': 'Karen',
        'location': 10,  # Sunset District
        'available_start': 990,  # 4:30 PM
        'available_end': 1320,  # 10:00 PM
        'duration': 105
    }
]

# Travel time matrix
travel_time_matrix = [
    [0, 10, 22, 19, 19, 11, 20, 15, 21, 9, 30],  # FD
    [11, 0, 17, 26, 22, 7, 27, 9, 18, 13, 27],   # FW
    [23, 19, 0, 31, 15, 14, 21, 11, 7, 22, 15],  # P
    [19, 25, 32, 0, 19, 23, 19, 27, 25, 18, 23], # B
    [21, 23, 15, 18, 0, 17, 6, 17, 10, 19, 15],  # HA
    [11, 7, 14, 23, 17, 0, 21, 7, 14, 10, 23],   # RH
    [21, 24, 20, 19, 6, 18, 0, 21, 16, 19, 17],  # C
    [17, 10, 10, 27, 16, 8, 22, 0, 11, 16, 19],  # MD
    [22, 18, 7, 27, 10, 14, 16, 9, 0, 21, 11],   # RD
    [9, 15, 24, 15, 18, 13, 17, 18, 20, 0, 27],  # US
    [30, 29, 16, 22, 15, 24, 17, 21, 12, 30, 0]  # SD
]

locations = [
    'Financial District',
    'Fisherman\'s Wharf',
    'Presidio',
    'Bayview',
    'Haight-Ashbury',
    'Russian Hill',
    'The Castro',
    'Marina District',
    'Richmond District',
    'Union Square',
    'Sunset District'
]

solver = Optimize()

# Define friend_loc for each friend (0-9)
friend_loc = [ Int(f'friend_loc_{i}') for i in range(10) ]
for i in range(10):
    solver.add(friend_loc[i] == friends[i]['location'])

# Define travel_time matrix in Z3
travel_time = [[ Int(f'travel_time_{i}_{j}') for j in range(11)] for i in range(11)]
for i in range(11):
    for j in range(11):
        solver.add(travel_time[i][j] == travel_time_matrix[i][j])

# Define variables for steps
max_steps = 10
friend = [ Int(f'friend_{i}') for i in range(max_steps) ]
start_time = [ Int(f'start_time_{i}') for i in range(max_steps) ]
arrival_time = [ Int(f'arrival_time_{i}') for i in range(max_steps) ]

# Initial time is 9:00 AM = 540 minutes
initial_time = 540

# Constraints for each step
for i in range(max_steps):
    # If friend[i] is not -1, then all previous steps are not -1
    if i > 0:
        for j in range(i):
            solver.add(Implies(friend[i] != -1, friend[j] != -1))
    
    # Define duration, available_start, available_end for this step
    duration_expr = 0
    for f in range(10):
        duration_expr = If(friend[i] == f, friends[f]['duration'], duration_expr)
    duration_expr = If(friend[i] == -1, 0, duration_expr)
    
    available_start_expr = 0
    for f in range(10):
        available_start_expr = If(friend[i] == f, friends[f]['available_start'], available_start_expr)
    available_start_expr = If(friend[i] == -1, 0, available_start_expr)
    
    available_end_expr = 0
    for f in range(10):
        available_end_expr = If(friend[i] == f, friends[f]['available_end'], available_end_expr)
    available_end_expr = If(friend[i] == -1, 0, available_end_expr)
    
    # Add constraints for this step if friend[i] != -1
    solver.add(Implies(friend[i] != -1, start_time[i] >= arrival_time[i]))
    solver.add(Implies(friend[i] != -1, start_time[i] >= available_start_expr))
    solver.add(Implies(friend[i] != -1, start_time[i] + duration_expr <= available_end_expr))
    
    # Define arrival_time[i]
    if i == 0:
        # arrival_time[i] = initial_time + travel_time[0][friend_loc[friend[i]]]
        # Define current_loc_expr for friend[i]
        current_loc_expr = -1
        for f in range(10):
            current_loc_expr = If(friend[i] == f, friend_loc[f], current_loc_expr)
        current_loc_expr = If(friend[i] == -1, -1, current_loc_expr)
        solver.add(Implies(friend[i] != -1, arrival_time[i] == initial_time + travel_time[0][current_loc_expr]))
    else:
        # Define prev_loc_expr for friend[i-1]
        prev_loc_expr = -1
        for f in range(10):
            prev_loc_expr = If(friend[i-1] == f, friend_loc[f], prev_loc_expr)
        prev_loc_expr = If(friend[i-1] == -1, -1, prev_loc_expr)
        
        # Define current_loc_expr for friend[i]
        current_loc_expr = -1
        for f in range(10):
            current_loc_expr = If(friend[i] == f, friend_loc[f], current_loc_expr)
        current_loc_expr = If(friend[i] == -1, -1, current_loc_expr)
        
        # Define duration_prev_expr for friend[i-1]
        duration_prev_expr = 0
        for f in range(10):
            duration_prev_expr = If(friend[i-1] == f, friends[f]['duration'], duration_prev_expr)
        duration_prev_expr = If(friend[i-1] == -1, 0, duration_prev_expr)
        
        # arrival_time[i] = start_time[i-1] + duration_prev_expr + travel_time[prev_loc_expr][current_loc_expr]
        solver.add(Implies(
            friend[i] != -1,
            arrival_time[i] == start_time[i-1] + duration_prev_expr + travel_time[prev_loc_expr][current_loc_expr]
        ))

# Maximize the number of friends met
count = Sum([ If(friend[i] != -1, 1, 0) for i in range(max_steps) ])
solver.maximize(count)

# Solve
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(max_steps):
        f_val = model.evaluate(friend[i])
        if f_val != -1:
            friend_index = f_val.as_long()
            st = model.evaluate(start_time[i]).as_long()
            duration = friends[friend_index]['duration']
            end_time = st + duration
            start_time_str = convert_minutes_to_time(st)
            end_time_str = convert_minutes_to_time(end_time)
            person = friends[friend_index]['name']
            location_index = friends[friend_index]['location']
            location_name = locations[location_index]
            itinerary.append({
                "action": "meet",
                "location": location_name,
                "person": person,
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")