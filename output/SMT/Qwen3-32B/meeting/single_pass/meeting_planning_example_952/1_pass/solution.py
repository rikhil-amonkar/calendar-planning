from z3 import *
import json

# Define friends' data
friends_data = [
    {
        'name': 'Richard',
        'location': "Fisherman's Wharf",
        'available_start': 11 * 60,  # 11:00 AM
        'available_end': 12 * 60 + 45,  # 12:45 PM
        'duration': 60,
    },
    {
        'name': 'Elizabeth',
        'location': "Nob Hill",
        'available_start': 11 * 60 + 45,  # 11:45 AM
        'available_end': 18 * 60 + 30,  # 6:30 PM
        'duration': 75,
    },
    {
        'name': 'Brian',
        'location': "North Beach",
        'available_start': 13 * 60,  # 1:00 PM
        'available_end': 19 * 60,  # 7:00 PM
        'duration': 90,
    },
    {
        'name': 'Ashley',
        'location': "Haight-Ashbury",
        'available_start': 15 * 60,  # 3:00 PM
        'available_end': 20 * 60 + 30,  # 8:30 PM
        'duration': 90,
    },
    {
        'name': 'Jessica',
        'location': "Golden Gate Park",
        'available_start': 20 * 60,  # 8:00 PM
        'available_end': 21 * 60 + 45,  # 9:45 PM
        'duration': 105,
    },
    {
        'name': 'Deborah',
        'location': "Union Square",
        'available_start': 17 * 60 + 30,  # 5:30 PM
        'available_end': 22 * 60,  # 10:00 PM
        'duration': 60,
    },
    {
        'name': 'Kimberly',
        'location': "Alamo Square",
        'available_start': 17 * 60 + 30,  # 5:30 PM
        'available_end': 21 * 60 + 15,  # 9:15 PM
        'duration': 45,
    },
    {
        'name': 'Matthew',
        'location': "Presidio",
        'available_start': 8 * 60 + 15,  # 8:15 AM
        'available_end': 9 * 60,  # 9:00 AM
        'duration': 15,
    },
    {
        'name': 'Kenneth',
        'location': "Chinatown",
        'available_start': 13 * 60 + 45,  # 1:45 PM
        'available_end': 19 * 60 + 30,  # 7:30 PM
        'duration': 105,
    },
    {
        'name': 'Anthony',
        'location': "Pacific Heights",
        'available_start': 14 * 60 + 15,  # 2:15 PM
        'available_end': 16 * 60,  # 4:00 PM
        'duration': 30,
    },
]

# Define locations and their indices
locations = {
    "Bayview": 0,
    "North Beach": 1,
    "Fisherman's Wharf": 2,
    "Haight-Ashbury": 3,
    "Nob Hill": 4,
    "Golden Gate Park": 5,
    "Union Square": 6,
    "Alamo Square": 7,
    "Presidio": 8,
    "Chinatown": 9,
    "Pacific Heights": 10,
}

# Define travel times between locations
travel_times = [
    [0, 22, 25, 19, 20, 22, 18, 16, 32, 19, 23],  # Bayview
    [25, 0, 5, 18, 7, 22, 7, 16, 17, 6, 8],       # North Beach
    [26, 6, 0, 22, 11, 25, 13, 21, 17, 12, 12],   # Fisherman's Wharf
    [18, 19, 23, 0, 15, 7, 19, 5, 15, 19, 12],    # Haight-Ashbury
    [19, 8, 10, 13, 0, 17, 7, 11, 17, 6, 8],      # Nob Hill
    [23, 23, 24, 7, 20, 0, 22, 9, 11, 23, 16],    # Golden Gate Park
    [15, 10, 15, 18, 9, 22, 0, 15, 24, 7, 15],    # Union Square
    [16, 15, 19, 5, 11, 9, 14, 0, 17, 15, 10],    # Alamo Square
    [31, 18, 19, 15, 18, 12, 22, 19, 0, 21, 11],  # Presidio
    [20, 3, 8, 19, 9, 23, 7, 17, 19, 0, 10],      # Chinatown
    [22, 9, 13, 11, 8, 15, 12, 10, 11, 11, 0],    # Pacific Heights
]

# Create friend_locations list
friend_locations = [locations[f['location']] for f in friends_data]

# Initialize solver
s = Optimize()

# Declare functions
travel_time_func = Function('travel_time', IntSort(), IntSort(), IntSort())
friend_to_loc = Function('friend_to_loc', IntSort(), IntSort())
available_start_func = Function('available_start', IntSort(), IntSort())
available_end_func = Function('available_end', IntSort(), IntSort())
duration_func = Function('duration', IntSort(), IntSort())

# Add travel time constraints
for i in range(11):
    for j in range(11):
        s.add(travel_time_func(i, j) == travel_times[i][j])

# Add friend_to_loc constraints
for i in range(10):
    s.add(friend_to_loc(i) == friend_locations[i])
s.add(friend_to_loc(-1) == 0)

# Add available_start, available_end, duration constraints
for i in range(10):
    s.add(available_start_func(i) == friends_data[i]['available_start'])
    s.add(available_end_func(i) == friends_data[i]['available_end'])
    s.add(duration_func(i) == friends_data[i]['duration'])

# Define variables
friends = [Int(f"friend_{i}") for i in range(10)]
start_times = [Int(f"start_time_{i}") for i in range(10)]
end_times = [Int(f"end_time_{i}") for i in range(10)]
locs = [Int(f"loc_{i}") for i in range(10)]
times = [Int(f"time_{i}") for i in range(10)]

# Add constraints for each step
for i in range(10):
    s.add(And(friends[i] >= -1, friends[i] <= 9))

for i in range(10):
    if i == 0:
        prev_time = 540
        prev_loc = 0
    else:
        prev_time = times[i-1]
        prev_loc = locs[i-1]

    curr_loc_i = If(friends[i] != -1, friend_to_loc(friends[i]), prev_loc)
    s.add(locs[i] == curr_loc_i)

    travel_time_i = travel_time_func(prev_loc, curr_loc_i)
    arrival_time_i = prev_time + travel_time_i

    s.add(Implies(friends[i] != -1, start_times[i] >= arrival_time_i))
    s.add(Implies(friends[i] != -1, start_times[i] >= available_start_func(friends[i])))
    s.add(Implies(friends[i] != -1, start_times[i] + duration_func(friends[i]) <= available_end_func(friends[i])))
    s.add(Implies(friends[i] != -1, end_times[i] == start_times[i] + duration_func(friends[i])))
    s.add(Implies(friends[i] != -1, times[i] == end_times[i]))
    s.add(Implies(friends[i] == -1, times[i] == prev_time))

# Add constraints to avoid duplicate friends
for i in range(10):
    for j in range(i+1, 10):
        s.add(Implies(And(friends[i] != -1, friends[j] != -1), friends[i] != friends[j]))

# Maximize the number of friends met
count = 0
for i in range(10):
    count += If(friends[i] != -1, 1, 0)
s.maximize(count)

# Solve the problem
if s.check() == sat:
    m = s.model()
    meetings = []
    for i in range(10):
        friend_idx = m.eval(friends[i])
        if friend_idx != -1:
            friend_name = friends_data[friend_idx.as_long()]['name']
            start_time = m.eval(start_times[i]).as_long()
            duration = friends_data[friend_idx.as_long()]['duration']
            end_time = start_time + duration
            start_h = start_time // 60
            start_m = start_time % 60
            end_h = end_time // 60
            end_m = end_time % 60
            meetings.append({
                "action": "meet",
                "person": friend_name,
                "start_time": f"{start_h:02d}:{start_m:02d}",
                "end_time": f"{end_h:02d}:{end_m:02d}"
            })
    print("SOLUTION:")
    print(json.dumps({"itinerary": meetings}))
else:
    print("No solution found.")