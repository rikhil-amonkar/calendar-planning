from z3 import *
import json

# Parse travel times
travel_time = {
    # Russian Hill
    ('Russian Hill', 'Marina District'): 7,
    ('Russian Hill', 'Financial District'): 11,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Bayview'): 23,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Nob Hill'): 5,
    # Marina District
    ('Marina District', 'Russian Hill'): 8,
    ('Marina District', 'Financial District'): 17,
    ('Marina District', 'Alamo Square'): 15,
    ('Marina District', 'Golden Gate Park'): 18,
    ('Marina District', 'The Castro'): 22,
    ('Marina District', 'Bayview'): 27,
    ('Marina District', 'Sunset District'): 19,
    ('Marina District', 'Haight-Ashbury'): 16,
    ('Marina District', 'Nob Hill'): 12,
    # Financial District
    ('Financial District', 'Russian Hill'): 11,
    ('Financial District', 'Marina District'): 15,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'The Castro'): 20,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Nob Hill'): 8,
    # Alamo Square
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Marina District'): 15,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'The Castro'): 8,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Nob Hill'): 11,
    # Golden Gate Park
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Marina District'): 16,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Nob Hill'): 20,
    # The Castro
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Marina District'): 21,
    ('The Castro', 'Financial District'): 21,
    ('The Castro', 'Alamo Square'): 8,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Bayview'): 19,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Nob Hill'): 16,
    # Bayview
    ('Bayview', 'Russian Hill'): 23,
    ('Bayview', 'Marina District'): 27,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'The Castro'): 19,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Nob Hill'): 20,
    # Sunset District
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Marina District'): 21,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Bayview'): 22,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Nob Hill'): 27,
    # Haight-Ashbury
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Marina District'): 17,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    # Nob Hill
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Marina District'): 11,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Bayview'): 19,
    ('Nob Hill', 'Sunset District'): 24,
    ('Nob Hill', 'Haight-Ashbury'): 13,
}

# Define friends
friends = [
    {
        'name': 'Karen',
        'location': 'Financial District',
        'available_start': 9 * 60 + 30,  # 9:30 AM
        'available_end': 12 * 60 + 45,   # 12:45 PM
        'required_duration': 90,
    },
    {
        'name': 'Barbara',
        'location': 'Alamo Square',
        'available_start': 10 * 60 + 0,
        'available_end': 18 * 60 + 30,
        'required_duration': 90,
    },
    {
        'name': 'David',
        'location': 'The Castro',
        'available_start': 9 * 60 + 0,
        'available_end': 18 * 60 + 0,
        'required_duration': 120,
    },
    {
        'name': 'Kevin',
        'location': 'Sunset District',
        'available_start': 10 * 60 + 0,
        'available_end': 17 * 60 + 45,
        'required_duration': 120,
    },
    {
        'name': 'Matthew',
        'location': 'Haight-Ashbury',
        'available_start': 10 * 60 + 15,
        'available_end': 15 * 60 + 30,
        'required_duration': 45,
    },
    {
        'name': 'Andrew',
        'location': 'Nob Hill',
        'available_start': 11 * 60 + 45,
        'available_end': 16 * 60 + 45,
        'required_duration': 105,
    },
    {
        'name': 'Nancy',
        'location': 'Golden Gate Park',
        'available_start': 16 * 60 + 45,
        'available_end': 20 * 60 + 0,
        'required_duration': 105,
    },
    {
        'name': 'Linda',
        'location': 'Bayview',
        'available_start': 18 * 60 + 15,
        'available_end': 19 * 60 + 45,
        'required_duration': 45,
    },
    {
        'name': 'Mark',
        'location': 'Marina District',
        'available_start': 18 * 60 + 45,
        'available_end': 21 * 60 + 0,
        'required_duration': 90,
    }
]

# Precompute travel times between friends
locations_for_friends = [f['location'] for f in friends]
travel_time_between = [[0]*9 for _ in range(9)]
for i in range(9):
    for j in range(9):
        loc_i = locations_for_friends[i]
        loc_j = locations_for_friends[j]
        travel_time_between[i][j] = travel_time.get((loc_i, loc_j), 0)

# Z3 setup
opt = Optimize()

seq_length = 9
friend_at_position = [Int(f"friend_at_position_{i}") for i in range(seq_length)]
arrival_time = [Int(f"arrival_time_{i}") for i in range(seq_length)]
start_time = [Int(f"start_time_{i}") for i in range(seq_length)]
end_time = [Int(f"end_time_{i}") for i in range(seq_length)]

# Constraint: each friend_at_position is -1 or 0-8
for i in range(seq_length):
    opt.add(Or([friend_at_position[i] == -1] + [friend_at_position[i] == j for j in range(9)]))

# Constraint: each friend appears at most once
for j in range(9):
    for i in range(seq_length):
        for k in range(i+1, seq_length):
            opt.add(Implies(And(friend_at_position[i] == j, friend_at_position[k] == j), False))

# Precompute travel time from Russian Hill to each friend
travel_time_from_russial_hill_to_friend = [travel_time[('Russian Hill', f['location'])] for f in friends]

# Declare travel_time_between function
travel_time_between_func = Function('travel_time_between', IntSort(), IntSort(), IntSort())

# Add constraints for travel_time_between
for i in range(9):
    for j in range(9):
        opt.add(travel_time_between_func(i, j) == travel_time_between[i][j])

# Add constraints for each position
for i in range(seq_length):
    is_valid = friend_at_position[i] != -1
    if i == 0:
        opt.add(Implies(is_valid, 
                        arrival_time[i] == 540 + travel_time_from_russial_hill_to_friend[friend_at_position[i]]))
    else:
        prev_friend = friend_at_position[i-1]
        current_friend = friend_at_position[i]
        prev_valid = prev_friend != -1
        opt.add(Implies(And(is_valid, prev_valid),
                        arrival_time[i] == end_time[i-1] + travel_time_between_func(prev_friend, current_friend)))
    opt.add(Implies(is_valid, start_time[i] >= arrival_time[i]))
    opt.add(Implies(is_valid, start_time[i] >= friends[friend_at_position[i]]['available_start']))
    opt.add(Implies(is_valid, end_time[i] == start_time[i] + friends[friend_at_position[i]]['required_duration']))
    opt.add(Implies(is_valid, end_time[i] <= friends[friend_at_position[i]]['available_end']))

# Maximize the number of friends included
num_friends = Sum([If(friend_at_position[i] != -1, 1, 0) for i in range(seq_length)])
opt.maximize(num_friends)

# Solve
result = opt.check()
if result == sat:
    model = opt.model()
    sequence = []
    for i in range(seq_length):
        fid = model.eval(friend_at_position[i]).as_long()
        if fid != -1:
            sequence.append(fid)
    # Build itinerary
    itinerary = []
    current_time = 540  # 9:00 AM
    current_location = 'Russian Hill'
    for fid in sequence:
        loc = friends[fid]['location']
        travel_time_to_loc = travel_time[(current_location, loc)]
        arrival_time = current_time + travel_time_to_loc
        available_start = friends[fid]['available_start']
        start_time = max(arrival_time, available_start)
        required_duration = friends[fid]['required_duration']
        end_time = start_time + required_duration
        itinerary.append({
            'action': 'meet',
            'person': friends[fid]['name'],
            'start_time': f"{start_time // 60:02d}:{start_time % 60:02d}",
            'end_time': f"{end_time // 60:02d}:{end_time % 60:02d}"
        })
        current_time = end_time
        current_location = loc
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found")