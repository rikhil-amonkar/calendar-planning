from z3 import *
import json
from datetime import datetime

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def parse_time(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

# Define friends data
friends_data = [
    {
        'name': 'David',
        'location': 'Mission District',
        'available_start': 480,  # 8:00 AM
        'available_end': 1185,   # 7:45 PM
        'min_duration': 45
    },
    {
        'name': 'Kenneth',
        'location': 'Alamo Square',
        'available_start': 840,  # 2:00 PM
        'available_end': 1185,   # 7:45 PM
        'min_duration': 120
    },
    {
        'name': 'John',
        'location': 'Pacific Heights',
        'available_start': 1020, # 5:00 PM
        'available_end': 1200,   # 8:00 PM
        'min_duration': 15
    },
    {
        'name': 'Charles',
        'location': 'Union Square',
        'available_start': 1305, # 9:45 PM
        'available_end': 1365,   # 10:45 PM
        'min_duration': 60
    },
    {
        'name': 'Deborah',
        'location': 'Golden Gate Park',
        'available_start': 420,  # 7:00 AM
        'available_end': 1095,   # 6:15 PM
        'min_duration': 90
    },
    {
        'name': 'Karen',
        'location': 'Sunset District',
        'available_start': 1065, # 5:45 PM
        'available_end': 1275,   # 9:15 PM
        'min_duration': 15
    },
    {
        'name': 'Carol',
        'location': 'Presidio',
        'available_start': 495,  # 8:15 AM
        'available_end': 555,    # 9:15 AM
        'min_duration': 30
    }
]

# Travel times between locations
travel_time_dict = {
    ('Chinatown', 'Mission District'): 18,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Pacific Heights'): 10,
    ('Chinatown', 'Union Square'): 7,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Presidio'): 19,
    ('Mission District', 'Chinatown'): 16,
    ('Mission District', 'Alamo Square'): 11,
    ('Mission District', 'Pacific Heights'): 16,
    ('Mission District', 'Union Square'): 15,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Presidio'): 25,
    ('Alamo Square', 'Chinatown'): 16,
    ('Alamo Square', 'Mission District'): 10,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Alamo Square', 'Union Square'): 14,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Presidio'): 18,
    ('Pacific Heights', 'Chinatown'): 11,
    ('Pacific Heights', 'Mission District'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Presidio'): 11,
    ('Union Square', 'Chinatown'): 7,
    ('Union Square', 'Mission District'): 14,
    ('Union Square', 'Alamo Square'): 15,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Golden Gate Park'): 22,
    ('Union Square', 'Sunset District'): 26,
    ('Union Square', 'Presidio'): 24,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Golden Gate Park', 'Union Square'): 22,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Union Square'): 30,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Presidio'): 16,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Pacific Heights'): 11,
    ('Presidio', 'Union Square'): 22,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Sunset District'): 15,
}

# Friend locations
friend_locations = [f['location'] for f in friends_data]

# Precompute travel times between friends
travel_time_between_friends = [[0 for _ in range(7)] for _ in range(7)]
for i in range(7):
    for j in range(7):
        from_loc = friend_locations[i]
        to_loc = friend_locations[j]
        travel_time_between_friends[i][j] = travel_time_dict[(from_loc, to_loc)]

# Precompute travel times from Chinatown to each friend's location
travel_time_chinatown_to_friend = [travel_time_dict[('Chinatown', loc)] for loc in friend_locations]

# Z3 variables
friends = [Int(f'friend_{i}') for i in range(7)]
starts = [Int(f'start_{i}') for i in range(7)]
ends = [Int(f'end_{i}') for i in range(7)]

# Create arrays for available_start, available_end, min_duration
available_start_arr = Array('available_start', IntSort(), IntSort())
available_end_arr = Array('available_end', IntSort(), IntSort())
min_duration_arr = Array('min_duration', IntSort(), IntSort())
for i in range(7):
    available_start_arr = Store(available_start_arr, i, friends_data[i]['available_start'])
    available_end_arr = Store(available_end_arr, i, friends_data[i]['available_end'])
    min_duration_arr = Store(min_duration_arr, i, friends_data[i]['min_duration'])

# Travel time from Chinatown to friend's location
chinatown_tt = Array('chinatown_tt', IntSort(), IntSort())
for i in range(7):
    chinatown_tt = Store(chinatown_tt, i, travel_time_chinatown_to_friend[i])

# Travel time between friends
travel_tt = Array('travel_tt', IntSort(), IntSort(), IntSort())
for i in range(7):
    for j in range(7):
        travel_tt = Store(travel_tt, i, Store(travel_tt[i], j, travel_time_between_friends[i][j]))

# Solver setup
s = Optimize()

# Add constraints for each step
for i in range(7):
    # If friend is not -1, then start and end constraints
    s.add(If(friends[i] != -1, starts[i] >= Select(available_start_arr, friends[i]), True))
    s.add(If(friends[i] != -1, ends[i] <= Select(available_end_arr, friends[i]), True))
    s.add(If(friends[i] != -1, ends[i] - starts[i] >= Select(min_duration_arr, friends[i]), True))
    # Start time must be >= arrival time + travel time from Chinatown
    s.add(If(friends[i] != -1, starts[i] >= 540 + Select(chinatown_tt, friends[i]), True))

# Add constraints for consecutive steps
for i in range(1, 7):
    # If current and previous are not -1, then current start >= previous end + travel time
    prev_friend = friends[i-1]
    curr_friend = friends[i]
    travel_time = Select(travel_tt, prev_friend, curr_friend)
    s.add(If(And(curr_friend != -1, prev_friend != -1), starts[i] >= ends[i-1] + travel_time, True))

# Add constraints that each friend is used at most once
for i in range(7):
    for j in range(i+1, 7):
        s.add(Or(friends[i] == -1, friends[j] == -1, friends[i] != friends[j]))

# Maximize the number of friends met
count = Sum([If(friends[i] != -1, 1, 0) for i in range(7)])
s.maximize(count)

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    # Extract the results
    used_steps = []
    for i in range(7):
        fi = model.evaluate(friends[i])
        if fi != -1:
            start = model.evaluate(starts[i])
            end = model.evaluate(ends[i])
            friend_info = friends_data[fi]
            used_steps.append({
                'action': 'meet',
                'location': friend_info['location'],
                'person': friend_info['name'],
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            })
    # Sort the used_steps by start time to ensure correct order
    used_steps.sort(key=lambda x: parse_time(x['start_time']))
    # Output the JSON
    print(json.dumps({'itinerary': used_steps}, indent=2))
else:
    print("No solution found")