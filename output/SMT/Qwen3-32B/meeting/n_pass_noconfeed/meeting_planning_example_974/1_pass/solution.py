from z3 import *
import json

# Define locations and travel times
locations = [
    'Sunset District', 'Presidio', 'Nob Hill', 'Pacific Heights',
    'Mission District', 'Marina District', 'North Beach', 'Russian Hill',
    'Richmond District', 'Embarcadero', 'Alamo Square'
]

# Travel time matrix (in minutes)
travel_time = [
    [0, 16, 27, 21, 25, 21, 28, 24, 12, 30, 17],
    [15, 0, 18, 11, 26, 11, 18, 14, 7, 20, 19],
    [24, 17, 0, 8, 13, 11, 8, 5, 14, 9, 11],
    [21, 11, 8, 0, 15, 6, 9, 7, 12, 10, 10],
    [24, 25, 12, 16, 0, 19, 17, 15, 20, 19, 11],
    [19, 10, 12, 7, 20, 0, 11, 8, 11, 14, 15],
    [27, 17, 7, 8, 18, 9, 0, 4, 18, 6, 16],
    [23, 14, 5, 7, 16, 7, 5, 0, 14, 8, 15],
    [11, 7, 17, 10, 20, 9, 17, 13, 0, 19, 13],
    [30, 20, 10, 11, 20, 12, 5, 8, 21, 0, 19],
    [16, 17, 11, 10, 10, 15, 15, 13, 11, 16, 0]
]

# Friend data: name, location index, available_start, available_end, min_duration
friends = [
    {'name': 'Charles', 'location': 1, 'available_start': 795, 'available_end': 900, 'min_duration': 105},
    {'name': 'Robert', 'location': 2, 'available_start': 795, 'available_end': 1050, 'min_duration': 90},
    {'name': 'Nancy', 'location': 3, 'available_start': 885, 'available_end': 1440, 'min_duration': 105},
    {'name': 'Brian', 'location': 4, 'available_start': 930, 'available_end': 1320, 'min_duration': 60},
    {'name': 'Kimberly', 'location': 5, 'available_start': 1020, 'available_end': 1185, 'min_duration': 75},
    {'name': 'David', 'location': 6, 'available_start': 885, 'available_end': 990, 'min_duration': 75},
    {'name': 'William', 'location': 7, 'available_start': 750, 'available_end': 1155, 'min_duration': 120},
    {'name': 'Jeffrey', 'location': 8, 'available_start': 720, 'available_end': 1155, 'min_duration': 45},
    {'name': 'Karen', 'location': 9, 'available_start': 855, 'available_end': 1245, 'min_duration': 60},
    {'name': 'Joshua', 'location': 10, 'available_start': 1125, 'available_end': 1320, 'min_duration': 60}
]

# Z3 solver setup
solver = Optimize()

MAX_EVENTS = 11
friends_vars = [Int(f"friend_{i}") for i in range(MAX_EVENTS)]
start_vars = [Int(f"start_{i}") for i in range(MAX_EVENTS)]
end_vars = [Int(f"end_{i}") for i in range(MAX_EVENTS)]
arrival_vars = [Int(f"arrival_{i}") for i in range(MAX_EVENTS)]

# Constraints for each event
for i in range(MAX_EVENTS):
    # Friend can be -1 (not used) or 0-9 (friend index)
    solver.add(friends_vars[i] >= -1)
    solver.add(friends_vars[i] <= 9)

    # Define arrival time
    if i == 0:
        # First event: arrival time is 9:00AM (540) + travel time from Sunset District
        arrival = 540
        for j in range(10):
            loc = friends[j]['location']
            arrival = If(friends_vars[i] == j, arrival + travel_time[0][loc], arrival)
        arrival_vars[i] = arrival
    else:
        # Subsequent events: arrival time is previous end time + travel time
        prev_arrival = end_vars[i-1]
        for j in range(10):
            prev_loc = friends[j]['location']
            for k in range(10):
                curr_loc = friends[k]['location']
                prev_arrival = If(And(friends_vars[i-1] == j, friends_vars[i] == k), 
                                  prev_arrival + travel_time[prev_loc][curr_loc], 
                                  prev_arrival)
        arrival_vars[i] = prev_arrival

    # If friend is included, apply constraints
    solver.add(Implies(friends_vars[i] != -1, start_vars[i] >= arrival_vars[i]))
    solver.add(Implies(friends_vars[i] != -1, end_vars[i] == start_vars[i] + (end_vars[i] - start_vars[i])))
    solver.add(Implies(friends_vars[i] != -1, end_vars[i] - start_vars[i] >= friends[friends_vars[i]]['min_duration']))
    solver.add(Implies(friends_vars[i] != -1, start_vars[i] >= friends[friends_vars[i]]['available_start']))
    solver.add(Implies(friends_vars[i] != -1, end_vars[i] <= friends[friends_vars[i]]['available_end']))

# Ensure each friend is used at most once
for j in range(10):
    count = 0
    for i in range(MAX_EVENTS):
        count += If(friends_vars[i] == j, 1, 0)
    solver.add(count <= 1)

# Maximize number of friends met
num_friends_met = 0
for i in range(MAX_EVENTS):
    num_friends_met += If(friends_vars[i] != -1, 1, 0)
solver.maximize(num_friends_met)

# Solve and output results
result = solver.check()
if result == sat:
    model = solver.model()
    itinerary = []
    for i in range(MAX_EVENTS):
        friend_idx = model.evaluate(friends_vars[i]).as_long()
        if friend_idx != -1:
            start = model.evaluate(start_vars[i]).as_long()
            end = model.evaluate(end_vars[i]).as_long()
            name = friends[friend_idx]['name']
            loc = locations[friends[friend_idx]['location']]
            def to_time_str(m):
                h, m = divmod(m, 60)
                return f"{h}:{m:02d}"
            itinerary.append({
                "action": "meet",
                "location": loc,
                "person": name,
                "start_time": to_time_str(start),
                "end_time": to_time_str(end)
            })
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))