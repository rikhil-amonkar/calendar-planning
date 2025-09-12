import json
from z3 import *

# Define friends and their parameters
friends = [
    {'name': 'Matthew', 'location': 'Presidio', 'available_start': 660, 'available_end': 1080, 'min_duration': 90},
    {'name': 'Margaret', 'location': 'Chinatown', 'available_start': 555, 'available_end': 1245, 'min_duration': 90},
    {'name': 'Nancy', 'location': 'Pacific Heights', 'available_start': 855, 'available_end': 1140, 'min_duration': 15},
    {'name': 'Helen', 'location': 'Richmond District', 'available_start': 1065, 'available_end': 1200, 'min_duration': 60},
    {'name': 'Rebecca', 'location': "Fisherman's Wharf", 'available_start': 1155, 'available_end': 1215, 'min_duration': 60},
    {'name': 'Kimberly', 'location': 'Golden Gate Park', 'available_start': 780, 'available_end': 930, 'min_duration': 120},
    {'name': 'Kenneth', 'location': 'Bayview', 'available_start': 930, 'available_end': 1140, 'min_duration': 60}
]

# Define all locations and their indices
all_locations = ['Russian Hill', 'Presidio', 'Chinatown', 'Pacific Heights', 'Richmond District', "Fisherman's Wharf", 'Golden Gate Park', 'Bayview']
location_to_index = {loc: idx for idx, loc in enumerate(all_locations)}
friend_to_loc = [location_to_index[f['location']] for f in friends]

# Define travel_matrix as 8x8
travel_matrix = [
    # From Russian Hill (0)
    [0, 14, 9, 7, 14, 7, 21, 23],
    # From Presidio (1)
    [14, 0, 21, 11, 7, 19, 12, 31],
    # From Chinatown (2)
    [7, 19, 0, 10, 20, 8, 23, 22],
    # From Pacific Heights (3)
    [7, 11, 11, 0, 12, 13, 15, 22],
    # From Richmond District (4)
    [13, 7, 20, 10, 0, 18, 9, 26],
    # From Fisherman's Wharf (5)
    [7, 17, 12, 12, 18, 0, 25, 26],
    # From Golden Gate Park (6)
    [19, 11, 23, 16, 7, 24, 0, 23],
    # From Bayview (7)
    [23, 31, 18, 23, 25, 25, 22, 0],
]

# Flatten the travel_matrix into a 1D list for Z3 array
travel_time_flat = []
for i in range(8):
    for j in range(8):
        travel_time_flat.append(travel_matrix[i][j])

# Create Z3 solver
solver = Optimize()

num_steps = 7  # number of friends

# Create Z3 variables
friends_vars = [Int(f'friend_{i}') for i in range(num_steps)]
is_used = [Bool(f'is_used_{i}') for i in range(num_steps)]
start_times = [Int(f'start_{i}') for i in range(num_steps)]

# Create arrays for friend_to_loc, available_start, available_end, min_duration
friend_to_loc_array = Array('friend_to_loc_array', IntSort(), IntSort())
available_start_array = Array('available_start_array', IntSort(), IntSort())
available_end_array = Array('available_end_array', IntSort(), IntSort())
min_duration_array = Array('min_duration_array', IntSort(), IntSort())
travel_time_array = Array('travel_time_array', IntSort(), IntSort())

# Initialize arrays with friend data
for i in range(7):
    friend_to_loc_array = Store(friend_to_loc_array, i, friend_to_loc[i])
    available_start_array = Store(available_start_array, i, friends[i]['available_start'])
    available_end_array = Store(available_end_array, i, friends[i]['available_end'])
    min_duration_array = Store(min_duration_array, i, friends[i]['min_duration'])

# Initialize travel_time_array with flat data
for idx, val in enumerate(travel_time_flat):
    travel_time_array = Store(travel_time_array, idx, val)

# Constraints for contiguous usage
for i in range(1, num_steps):
    solver.add(Implies(is_used[i], is_used[i-1]))

# Constraints: each friend is used at most once
for i in range(num_steps):
    for j in range(i+1, num_steps):
        solver.add(Implies(And(is_used[i], is_used[j]), friends_vars[i] != friends_vars[j]))

# Constraints for friend indices
for i in range(num_steps):
    solver.add(Implies(is_used[i], And(friends_vars[i] >= 0, friends_vars[i] <= 6)))

# Constraints for start times and travel times
for i in range(num_steps):
    # Available start and end time constraints
    available_start_expr = Select(available_start_array, friends_vars[i])
    available_end_expr = Select(available_end_array, friends_vars[i])
    min_duration_expr = Select(min_duration_array, friends_vars[i])
    solver.add(Implies(is_used[i], start_times[i] >= available_start_expr))
    solver.add(Implies(is_used[i], start_times[i] + min_duration_expr <= available_end_expr))

    # Travel time constraints
    if i == 0:
        # First step: travel from Russian Hill (location 0)
        current_loc = Select(friend_to_loc_array, friends_vars[i])
        key = current_loc
        travel_time_expr = Select(travel_time_array, key)
        solver.add(Implies(is_used[i], start_times[i] >= 540 + travel_time_expr))
    else:
        # Subsequent steps: travel from previous friend's location
        prev_loc = Select(friend_to_loc_array, friends_vars[i-1])
        current_loc = Select(friend_to_loc_array, friends_vars[i])
        key = prev_loc * 8 + current_loc
        travel_time_expr = Select(travel_time_array, key)
        prev_end_expr = start_times[i-1] + Select(min_duration_array, friends_vars[i-1])
        solver.add(Implies(And(is_used[i], is_used[i-1]), start_times[i] >= prev_end_expr + travel_time_expr))

# Maximize the number of used steps
count_used = Sum([ If(is_used[i], 1, 0) for i in range(num_steps) ])
solver.maximize(count_used)

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(num_steps):
        if model.eval(is_used[i]).as_bool():
            friend_idx = model.eval(friends_vars[i]).as_long()
            start_time = model.eval(start_times[i]).as_long()
            min_duration = model.eval(Select(min_duration_array, friend_idx)).as_long()
            end_time = start_time + min_duration
            friend = friends[friend_idx]
            # Convert to time strings
            def to_time_str(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours}:{mins:02d}"
            start_str = to_time_str(start_time)
            end_str = to_time_str(end_time)
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": start_str,
                "end_time": end_str
            })
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"itinerary": []}))