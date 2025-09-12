import z3
import json

# Define friends with their availability and constraints
friends = [
    {'name': 'Matthew', 'location': 1, 'available_start': 990, 'available_end': 1200, 'min_duration': 45},
    {'name': 'Rebecca', 'location': 2, 'available_start': 915, 'available_end': 1155, 'min_duration': 105},
    {'name': 'Brian', 'location': 3, 'available_start': 855, 'available_end': 1320, 'min_duration': 30},
    {'name': 'Emily', 'location': 4, 'available_start': 675, 'available_end': 1185, 'min_duration': 15},
    {'name': 'Karen', 'location': 5, 'available_start': 705, 'available_end': 1050, 'min_duration': 30},
    {'name': 'Stephanie', 'location': 6, 'available_start': 780, 'available_end': 945, 'min_duration': 75},
    {'name': 'James', 'location': 7, 'available_start': 870, 'available_end': 1140, 'min_duration': 120},
    {'name': 'Steven', 'location': 8, 'available_start': 840, 'available_end': 1200, 'min_duration': 30},
    {'name': 'Elizabeth', 'location': 9, 'available_start': 780, 'available_end': 1035, 'min_duration': 120},
    {'name': 'William', 'location': 10, 'available_start': 1095, 'available_end': 1215, 'min_duration': 90},
]

# Location names for mapping
location_names = [
    "Richmond District",
    "The Castro",
    "Nob Hill",
    "Marina District",
    "Pacific Heights",
    "Haight-Ashbury",
    "Mission District",
    "Chinatown",
    "Russian Hill",
    "Alamo Square",
    "Bayview"
]

# Travel time matrix between locations (11x11)
travel_time = [[0 for _ in range(11)] for _ in range(11)]

# Fill travel times (as per input)
travel_time[0][1] = 16; travel_time[0][2] = 17; travel_time[0][3] = 9; travel_time[0][4] = 10; travel_time[0][5] = 10
travel_time[0][6] = 20; travel_time[0][7] = 20; travel_time[0][8] = 13; travel_time[0][9] = 13; travel_time[0][10] = 27

travel_time[1][0] = 16; travel_time[1][2] = 16; travel_time[1][3] = 21; travel_time[1][4] = 16; travel_time[1][5] = 6
travel_time[1][6] = 7; travel_time[1][7] = 22; travel_time[1][8] = 18; travel_time[1][9] = 8; travel_time[1][10] = 19

travel_time[2][0] = 14; travel_time[2][1] = 17; travel_time[2][3] = 11; travel_time[2][4] = 8; travel_time[2][5] = 13
travel_time[2][6] = 13; travel_time[2][7] = 6; travel_time[2][8] = 5; travel_time[2][9] = 11; travel_time[2][10] = 19

travel_time[3][0] = 11; travel_time[3][1] = 22; travel_time[3][2] = 12; travel_time[3][4] = 7; travel_time[3][5] = 16
travel_time[3][6] = 20; travel_time[3][7] = 15; travel_time[3][8] = 8; travel_time[3][9] = 15; travel_time[3][10] = 27

travel_time[4][0] = 12; travel_time[4][1] = 16; travel_time[4][2] = 8; travel_time[4][3] = 6; travel_time[4][5] = 11
travel_time[4][6] = 15; travel_time[4][7] = 11; travel_time[4][8] = 7; travel_time[4][9] = 10; travel_time[4][10] = 22

travel_time[5][0] = 10; travel_time[5][1] = 6; travel_time[5][2] = 15; travel_time[5][3] = 17; travel_time[5][4] = 12
travel_time[5][6] = 11; travel_time[5][7] = 19; travel_time[5][8] = 17; travel_time[5][9] = 5; travel_time[5][10] = 18

travel_time[6][0] = 20; travel_time[6][1] = 7; travel_time[6][2] = 12; travel_time[6][3] = 19; travel_time[6][4] = 16
travel_time[6][5] = 12; travel_time[6][7] = 16; travel_time[6][8] = 15; travel_time[6][9] = 11; travel_time[6][10] = 14

travel_time[7][0] = 20; travel_time[7][1] = 22; travel_time[7][2] = 9; travel_time[7][3] = 12; travel_time[7][4] = 10
travel_time[7][5] = 19; travel_time[7][6] = 17; travel_time[7][8] = 7; travel_time[7][9] = 17; travel_time[7][10] = 20

travel_time[8][0] = 14; travel_time[8][1] = 21; travel_time[8][2] = 5; travel_time[8][3] = 7; travel_time[8][4] = 7
travel_time[8][5] = 17; travel_time[8][6] = 16; travel_time[8][7] = 9; travel_time[8][9] = 15; travel_time[8][10] = 23

travel_time[9][0] = 11; travel_time[9][1] = 8; travel_time[9][2] = 11; travel_time[9][3] = 15; travel_time[9][4] = 10
travel_time[9][5] = 5; travel_time[9][6] = 10; travel_time[9][7] = 15; travel_time[9][8] = 13; travel_time[9][10] = 16

travel_time[10][0] = 25; travel_time[10][1] = 19; travel_time[10][2] = 20; travel_time[10][3] = 27; travel_time[10][4] = 23
travel_time[10][5] = 19; travel_time[10][6] = 13; travel_time[10][7] = 19; travel_time[10][8] = 23; travel_time[10][9] = 16

# Z3 solver setup
solver = z3.Optimize()

num_steps = 11
friends_vars = [z3.Int('friend_%d' % i) for i in range(num_steps)]
location_vars = [z3.Int('location_%d' % i) for i in range(num_steps)]
start_time_vars = [z3.Int('start_time_%d' % i) for i in range(num_steps)]
end_time_vars = [z3.Int('end_time_%d' % i) for i in range(num_steps)]

# Friend to location mapping
friend_to_location = [f['location'] for f in friends]

# Constraints: location[i] == friend_to_location[friend[i]] if friend[i] != -1
for i in range(num_steps):
    for k in range(len(friends)):
        solver.add(z3.If(friends_vars[i] == k, location_vars[i] == friend_to_location[k], True))

# Constraints: availability and duration for each friend
for i in range(num_steps):
    for k in range(len(friends)):
        solver.add(z3.If(friends_vars[i] == k, start_time_vars[i] >= friends[k]['available_start'], True))
        solver.add(z3.If(friends_vars[i] == k, end_time_vars[i] <= friends[k]['available_end'], True))
        solver.add(z3.If(friends_vars[i] == k, end_time_vars[i] - start_time_vars[i] >= friends[k]['min_duration'], True))

# Constraints: each friend can be scheduled at most once
for k in range(len(friends)):
    count = z3.Sum([z3.If(friends_vars[i] == k, 1, 0) for i in range(num_steps)])
    solver.add(count <= 1)

# Constraints: first step's start time and transitions between steps
for i in range(num_steps):
    if i == 0:
        # First step: Add constraints based on friend selected
        for k in range(len(friends)):
            solver.add(z3.If(friends_vars[i] == k, 
                             start_time_vars[i] >= 540 + travel_time[0][friend_to_location[k]], 
                             True))
    else:
        # Transitions between steps: Add constraints for all friend pairs
        for m in range(len(friends)):
            for k in range(len(friends)):
                solver.add(z3.If(z3.And(friends_vars[i-1] == m, friends_vars[i] == k),
                                 start_time_vars[i] >= end_time_vars[i-1] + travel_time[friend_to_location[m]][friend_to_location[k]],
                                 True))

# Maximize the number of friends met
num_friends = z3.Sum([z3.If(friends_vars[i] != -1, 1, 0) for i in range(num_steps)])
solver.maximize(num_friends)

# Solve and output the result
if solver.check() == z3.sat:
    model = solver.model()
    itinerary = []
    for i in range(num_steps):
        friend = model.eval(friends_vars[i])
        if friend != -1:
            friend_idx = friend.as_long()
            location = model.eval(location_vars[i]).as_long()
            start_time = model.eval(start_time_vars[i]).as_long()
            end_time = model.eval(end_time_vars[i]).as_long()
            name = friends[friend_idx]['name']
            def to_time_str(t):
                hours = t // 60
                minutes = t % 60
                return f"{hours}:{minutes:02d}"
            itinerary.append({
                "action": "meet",
                "location": location_names[location],
                "person": name,
                "start_time": to_time_str(start_time),
                "end_time": to_time_str(end_time)
            })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")