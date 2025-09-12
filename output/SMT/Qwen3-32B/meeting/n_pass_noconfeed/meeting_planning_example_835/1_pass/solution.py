import json
from z3 import *

# Define friends and their data
friends = [
    {'name': 'Helen', 'location': 1, 'start': 570, 'end': 735, 'duration': 45},
    {'name': 'Steven', 'location': 2, 'start': 1215, 'end': 1320, 'duration': 105},
    {'name': 'Deborah', 'location': 3, 'start': 510, 'end': 720, 'duration': 30},
    {'name': 'Matthew', 'location': 4, 'start': 555, 'end': 855, 'duration': 45},
    {'name': 'Joseph', 'location': 5, 'start': 855, 'end': 1125, 'duration': 120},
    {'name': 'Ronald', 'location': 6, 'start': 960, 'end': 1245, 'duration': 60},
    {'name': 'Robert', 'location': 7, 'start': 1110, 'end': 1275, 'duration': 120},
    {'name': 'Rebecca', 'location': 8, 'start': 885, 'end': 975, 'duration': 30},
    {'name': 'Elizabeth', 'location': 9, 'start': 1110, 'end': 1260, 'duration': 120},
]

# Define travel matrix
travel_times = [
    (0, 1, 15), (0, 2, 16), (0, 3, 22), (0, 4, 6), (0, 5, 12), (0, 6, 21), (0, 7, 10), (0, 8, 13), (0, 9, 15),
    (1, 0, 16), (1, 2, 13), (1, 3, 23), (1, 4, 16), (1, 5, 22), (1, 6, 10), (1, 7, 9), (1, 8, 26), (1, 9, 17),
    (2, 0, 16), (2, 1, 11), (2, 3, 19), (2, 4, 21), (2, 5, 19), (2, 6, 17), (2, 7, 8), (2, 8, 21), (2, 9, 7),
    (3, 0, 23), (3, 1, 22), (3, 2, 19), (3, 4, 27), (3, 5, 18), (3, 6, 23), (3, 7, 16), (3, 8, 19), (3, 9, 13),
    (4, 0, 7), (4, 1, 18), (4, 2, 22), (4, 3, 27), (4, 5, 16), (4, 6, 19), (4, 7, 15), (4, 8, 17), (4, 9, 20),
    (5, 0, 15), (5, 1, 22), (5, 2, 17), (5, 3, 15), (5, 4, 18), (5, 6, 27), (5, 7, 15), (5, 8, 9), (5, 9, 14),
    (6, 0, 21), (6, 1, 11), (6, 2, 17), (6, 3, 22), (6, 4, 21), (6, 5, 30), (6, 7, 17), (6, 8, 30), (6, 9, 25),
    (7, 0, 10), (7, 1, 9), (7, 2, 8), (7, 3, 16), (7, 4, 15), (7, 5, 14), (7, 6, 16), (7, 8, 17), (7, 9, 10),
    (8, 0, 13), (8, 1, 23), (8, 2, 20), (8, 3, 19), (8, 4, 15), (8, 5, 9), (8, 6, 30), (8, 7, 17), (8, 9, 17),
    (9, 0, 16), (9, 1, 17), (9, 2, 7), (9, 3, 14), (9, 4, 19), (9, 5, 15), (9, 6, 24), (9, 7, 11), (9, 8, 15),
]

travel_matrix = [[0 for _ in range(10)] for _ in range(10)]
for from_loc, to_loc, time in travel_times:
    travel_matrix[from_loc][to_loc] = time

# Define locations
locations = [
    "Pacific Heights",
    "Golden Gate Park",
    "The Castro",
    "Bayview",
    "Marina District",
    "Union Square",
    "Sunset District",
    "Alamo Square",
    "Financial District",
    "Mission District"
]

# Z3 setup
solver = Optimize()

# Define travel_time_func as a function from two integers to integer
travel_time_func = Function('travel_time_func', IntSort(), IntSort(), IntSort())
for from_loc in range(10):
    for to_loc in range(10):
        solver.add(travel_time_func(from_loc, to_loc) == travel_matrix[from_loc][to_loc])

# Define friend data arrays as Z3 arrays
friend_location = Array('friend_location', IntSort(), IntSort())
friend_start = Array('friend_start', IntSort(), IntSort())
friend_end = Array('friend_end', IntSort(), IntSort())
friend_duration = Array('friend_duration', IntSort(), IntSort())

for j in range(len(friends)):
    friend_location = Store(friend_location, j, friends[j]['location'])
    friend_start = Store(friend_start, j, friends[j]['start'])
    friend_end = Store(friend_end, j, friends[j]['end'])
    friend_duration = Store(friend_duration, j, friends[j]['duration'])

# Define variables for each step
max_meetings = 10
meet = [Bool(f"meet_{i}") for i in range(max_meetings)]
friend = [Int(f"friend_{i}") for i in range(max_meetings)]
start = [Int(f"start_{i}") for i in range(max_meetings)]
current_time = [Int(f"current_time_{i}") for i in range(max_meetings)]
current_location = [Int(f"current_location_{i}") for i in range(max_meetings)]

# Initial conditions for step 0
solver.add(Implies(meet[0], And(0 <= friend[0], friend[0] < len(friends))))

fl_0 = Select(friend_location, friend[0])
fs_0 = Select(friend_start, friend[0])
fe_0 = Select(friend_end, friend[0])
fd_0 = Select(friend_duration, friend[0])

solver.add(Implies(meet[0], start[0] >= 540 + travel_time_func(0, fl_0)))
solver.add(Implies(meet[0], start[0] >= fs_0))
solver.add(Implies(meet[0], start[0] + fd_0 <= fe_0))
solver.add(Implies(meet[0], current_time[0] == start[0] + fd_0))
solver.add(Implies(meet[0], current_location[0] == fl_0))
solver.add(Implies(Not(meet[0]), current_time[0] == 540))
solver.add(Implies(Not(meet[0]), current_location[0] == 0))

# Add constraints for steps 1 to 9
for i in range(1, max_meetings):
    solver.add(Implies(meet[i], And(0 <= friend[i], friend[i] < len(friends))))

    fl_i = Select(friend_location, friend[i])
    fs_i = Select(friend_start, friend[i])
    fe_i = Select(friend_end, friend[i])
    fd_i = Select(friend_duration, friend[i])

    solver.add(Implies(meet[i], start[i] >= current_time[i-1] + travel_time_func(current_location[i-1], fl_i)))
    solver.add(Implies(meet[i], start[i] >= fs_i))
    solver.add(Implies(meet[i], start[i] + fd_i <= fe_i))
    solver.add(Implies(meet[i], current_time[i] == start[i] + fd_i))
    solver.add(Implies(meet[i], current_location[i] == fl_i))
    solver.add(Implies(Not(meet[i]), current_time[i] == current_time[i-1]))
    solver.add(Implies(Not(meet[i]), current_location[i] == current_location[i-1]))

# Add constraints to ensure each friend is met at most once
for j in range(len(friends)):
    count = 0
    for i in range(max_meetings):
        count += If(And(meet[i], friend[i] == j), 1, 0)
    solver.add(count <= 1)

# Maximize the number of friends met
total_meet = 0
for i in range(max_meetings):
    total_meet += If(meet[i], 1, 0)
solver.maximize(total_meet)

# Check if the solver can find a solution
result = solver.check()
if result == sat:
    model = solver.model()
    # Extract the itinerary
    itinerary = []
    for i in range(max_meetings):
        if model.eval(meet[i]):
            friend_idx = model.eval(friend[i]).as_long()
            friend_data = friends[friend_idx]
            start_time = model.eval(start[i]).as_long()
            end_time = start_time + friend_data['duration']
            # Convert to H:MM format
            start_h = start_time // 60
            start_m = start_time % 60
            end_h = end_time // 60
            end_m = end_time % 60
            start_str = f"{start_h}:{start_m:02d}"
            end_str = f"{end_h}:{end_m:02d}"
            itinerary.append({
                "action": "meet",
                "location": locations[friend_data['location']],
                "person": friend_data['name'],
                "start_time": start_str,
                "end_time": end_str
            })
    # Sort by start time
    itinerary.sort(key=lambda x: x['start_time'])
    print(json.dumps({"itinerary": itinerary}))
else:
    print(json.dumps({"itinerary": []}))