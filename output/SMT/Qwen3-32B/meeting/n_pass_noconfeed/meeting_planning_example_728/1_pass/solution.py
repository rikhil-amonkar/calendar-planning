from z3 import *

# Define friends and their data
friends = [
    {
        'name': 'Karen',
        'location': 'Mission District',
        'available_start': 14*60 + 15,  # 855
        'available_end': 22*60,          # 1320
        'min_duration': 30
    },
    {
        'name': 'Richard',
        'location': "Fisherman's Wharf",
        'available_start': 14*60 + 30,   # 870
        'available_end': 17*60 + 30,     # 1050
        'min_duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Presidio',
        'available_start': 21*60 + 45,   # 1305
        'available_end': 22*60 + 45,     # 1365
        'min_duration': 60
    },
    {
        'name': 'Joseph',
        'location': 'Union Square',
        'available_start': 11*60 + 45,   # 705
        'available_end': 14*60 + 45,     # 885
        'min_duration': 120
    },
    {
        'name': 'Helen',
        'location': 'Sunset District',
        'available_start': 14*60 + 45,   # 885
        'available_end': 20*60 + 45,     # 1245
        'min_duration': 105
    },
    {
        'name': 'Elizabeth',
        'location': 'Financial District',
        'available_start': 10*60,        # 600
        'available_end': 12*60 + 45,     # 765
        'min_duration': 75
    },
    {
        'name': 'Kimberly',
        'location': 'Haight-Ashbury',
        'available_start': 14*60 + 15,   # 855
        'available_end': 17*60 + 30,     # 1050
        'min_duration': 105
    },
    {
        'name': 'Ashley',
        'location': 'Russian Hill',
        'available_start': 11*60 + 30,   # 690
        'available_end': 21*60 + 30,     # 1290
        'min_duration': 45
    },
]

# Define travel times between locations
travel_time_dict = {
    'Marina District': {
        'Mission District': 20,
        "Fisherman's Wharf": 10,
        'Presidio': 10,
        'Union Square': 16,
        'Sunset District': 19,
        'Financial District': 17,
        'Haight-Ashbury': 16,
        'Russian Hill': 8,
    },
    'Mission District': {
        'Marina District': 19,
        "Fisherman's Wharf": 22,
        'Presidio': 25,
        'Union Square': 15,
        'Sunset District': 24,
        'Financial District': 15,
        'Haight-Ashbury': 12,
        'Russian Hill': 15,
    },
    "Fisherman's Wharf": {
        'Marina District': 9,
        'Mission District': 22,
        'Presidio': 17,
        'Union Square': 13,
        'Sunset District': 27,
        'Financial District': 11,
        'Haight-Ashbury': 22,
        'Russian Hill': 7,
    },
    'Presidio': {
        'Marina District': 11,
        'Mission District': 26,
        "Fisherman's Wharf": 19,
        'Union Square': 22,
        'Sunset District': 15,
        'Financial District': 23,
        'Haight-Ashbury': 15,
        'Russian Hill': 14,
    },
    'Union Square': {
        'Marina District': 18,
        'Mission District': 14,
        "Fisherman's Wharf": 15,
        'Presidio': 24,
        'Sunset District': 27,
        'Financial District': 9,
        'Haight-Ashbury': 18,
        'Russian Hill': 13,
    },
    'Sunset District': {
        'Marina District': 21,
        'Mission District': 25,
        "Fisherman's Wharf": 29,
        'Presidio': 16,
        'Union Square': 30,
        'Financial District': 30,
        'Haight-Ashbury': 15,
        'Russian Hill': 24,
    },
    'Financial District': {
        'Marina District': 15,
        'Mission District': 17,
        "Fisherman's Wharf": 10,
        'Presidio': 22,
        'Union Square': 9,
        'Sunset District': 30,
        'Haight-Ashbury': 19,
        'Russian Hill': 11,
    },
    'Haight-Ashbury': {
        'Marina District': 17,
        'Mission District': 11,
        "Fisherman's Wharf": 23,
        'Presidio': 15,
        'Union Square': 19,
        'Sunset District': 15,
        'Financial District': 21,
        'Russian Hill': 17,
    },
    'Russian Hill': {
        'Marina District': 7,
        'Mission District': 16,
        "Fisherman's Wharf": 7,
        'Presidio': 14,
        'Union Square': 10,
        'Sunset District': 23,
        'Financial District': 11,
        'Haight-Ashbury': 17,
    },
}

# Prepare friends with location indices
locations = ['Marina District', 'Mission District', "Fisherman's Wharf", 'Presidio', 'Union Square', 'Sunset District', 'Financial District', 'Haight-Ashbury', 'Russian Hill']
loc_to_idx = {loc: i for i, loc in enumerate(locations)}

for f in friends:
    f['location_idx'] = loc_to_idx[f['location']]

# Build travel_time_matrix
travel_time_matrix = [[0 for _ in range(len(locations))] for _ in range(len(locations))]
for from_loc in locations:
    for to_loc in locations:
        travel_time_matrix[loc_to_idx[from_loc]][loc_to_idx[to_loc]] = travel_time_dict[from_loc][to_loc]

# Z3 setup
solver = Optimize()

max_meetings = 8
friend_idx = [Int(f'friend_idx_{i}') for i in range(max_meetings)]
start = [Int(f'start_{i}') for i in range(max_meetings)]
end = [Int(f'end_{i}') for i in range(max_meetings)]
current_location = [Int(f'current_location_{i}') for i in range(max_meetings)]
current_time = [Int(f'current_time_{i}') for i in range(max_meetings)]

# Constraints on friend_idx: 0-7 for friends, 8 for no friend
for i in range(max_meetings):
    solver.add(And(friend_idx[i] >= 0, friend_idx[i] <= 8))

# Constraints for each step
for i in range(max_meetings):
    # For each possible friend a (0-7), add constraints if friend_idx[i] == a
    for a in range(len(friends)):
        # start >= available_start
        solver.add(Implies(friend_idx[i] == a, start[i] >= friends[a]['available_start']))
        # end <= available_end
        solver.add(Implies(friend_idx[i] == a, end[i] <= friends[a]['available_end']))
        # end >= start + min_duration
        solver.add(Implies(friend_idx[i] == a, end[i] >= start[i] + friends[a]['min_duration']))

    # For step 0, add constraint on start time based on travel from Marina
    if i == 0:
        for a in range(len(friends)):
            from_loc = 'Marina District'
            to_loc = friends[a]['location']
            travel_time = travel_time_dict[from_loc][to_loc]
            solver.add(Implies(friend_idx[i] == a, start[i] >= 9*60 + travel_time))

# Constraints for current_location and current_time for each step
for i in range(max_meetings):
    if i == 0:
        # Step 0: if friend is selected, current_location and current_time are based on that
        # else, current_location is Marina District (0), current_time is 540
        solver.add(If(friend_idx[i] != 8, 
                      And(current_location[i] == friends[friend_idx[i]]['location_idx'], 
                          current_time[i] == end[i]),
                      And(current_location[i] == 0, 
                          current_time[i] == 540)))
    else:
        # Step i >= 1: if friend is selected, current_location and current_time are based on that
        # else, same as previous step
        solver.add(If(friend_idx[i] != 8, 
                      And(current_location[i] == friends[friend_idx[i]]['location_idx'], 
                          current_time[i] == end[i]),
                      And(current_location[i] == current_location[i-1], 
                          current_time[i] == current_time[i-1])))

# Constraints for travel time between previous location and current meeting location
for i in range(1, max_meetings):
    for a in range(len(friends)):
        for c in range(len(locations)):
            # If friend_idx[i] is a and current_location[i-1] is c, then start[i] >= current_time[i-1] + travel_time
            friend_loc = friends[a]['location_idx']
            travel_time = travel_time_matrix[c][friend_loc]
            solver.add(Implies(And(friend_idx[i] == a, current_location[i-1] == c), 
                               start[i] >= current_time[i-1] + travel_time))

# Constraints to prevent same friend from being selected twice
for i in range(max_meetings):
    for j in range(i+1, max_meetings):
        for a in range(len(friends)):
            solver.add(Implies(And(friend_idx[i] == a, friend_idx[j] == a), False))

# Objective: maximize the number of friends met
total_friends = Sum([If(friend_idx[i] != 8, 1, 0) for i in range(max_meetings)])
solver.maximize(total_friends)

# Check for solution
result = solver.check()
if result == sat:
    model = solver.model()
    # Extract the solution
    meetings = []
    for i in range(max_meetings):
        fid = model.eval(friend_idx[i]).as_long()
        if fid != 8:  # a friend is selected
            a = fid
            meeting_start = model.eval(start[i]).as_long()
            meeting_end = model.eval(end[i]).as_long()
            name = friends[a]['name']
            location = friends[a]['location']
            # Convert times to H:MM format
            def to_time_str(minutes):
                h = minutes // 60
                m = minutes % 60
                return f"{h}:{m:02d}"
            start_str = to_time_str(meeting_start)
            end_str = to_time_str(meeting_end)
            meetings.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
    # Output the JSON
    import json
    print(json.dumps({"itinerary": meetings}, indent=2))
else:
    print("No solution found")