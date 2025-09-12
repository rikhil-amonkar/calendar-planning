from z3 import *
import json

# Define friend information and travel times
friends_info = [
    {'name': 'Rebecca', 'location': 'Bayview', 'available_start': 540, 'available_end': 765},
    {'name': 'Amanda', 'location': 'Pacific Heights', 'available_start': 1050, 'available_end': 1245},
    {'name': 'James', 'location': 'Alamo Square', 'available_start': 585, 'available_end': 1275},
    {'name': 'Sarah', 'location': "Fisherman's Wharf", 'available_start': 480, 'available_end': 1230},
    {'name': 'Melissa', 'location': 'Golden Gate Park', 'available_start': 540, 'available_end': 1065},
]

# Travel times between friends (based on their locations)
friend_to_friend_travel_times = [
    [0, 23, 16, 25, 22],
    [22, 0, 10, 13, 15],
    [16, 10, 0, 19, 9],
    [26, 12, 20, 0, 25],
    [23, 16, 10, 24, 0],
]

MAX_STEPS = 5
solver = Optimize()

used = [Bool(f'used_{i}') for i in range(MAX_STEPS)]
friend = [Int(f'friend_{i}') for i in range(MAX_STEPS)]
start_time = [Int(f'start_time_{i}') for i in range(MAX_STEPS)]
end_time = [Int(f'end_time_{i}') for i in range(MAX_STEPS)]

# Constraints for friend indices
for i in range(MAX_STEPS):
    solver.add(And(friend[i] >= 0, friend[i] <= 4))

# Uniqueness constraints
for i in range(MAX_STEPS):
    for j in range(i + 1, MAX_STEPS):
        solver.add(Implies(And(used[i], used[j]), friend[i] != friend[j]))

# Helper function for travel times
def get_travel_time_expr(prev_friend, curr_friend):
    return friend_to_friend_travel_times[prev_friend][curr_friend]

# Add constraints for each step
for i in range(MAX_STEPS):
    if i == 0:
        # Travel from Castro to current friend's location
        current_loc = If(friend[i] == 0, 1,
                         If(friend[i] == 1, 2,
                            If(friend[i] == 2, 3,
                               If(friend[i] == 3, 4,
                                  If(friend[i] == 4, 5, 0))))
        travel_time_expr = If(current_loc == 1, 19,
                              If(current_loc == 2, 16,
                                 If(current_loc == 3, 8,
                                    If(current_loc == 4, 24,
                                       If(current_loc == 5, 11, 0))))
        arrival_time = 540 + travel_time_expr
    else:
        # Travel between previous friend and current friend
        travel_time_expr = get_travel_time_expr(friend[i-1], friend[i])
        arrival_time = end_time[i-1] + travel_time_expr

    # Available start and end times for the current friend
    available_start_expr = If(friend[i] == 0, 540,
                              If(friend[i] == 1, 1050,
                                 If(friend[i] == 2, 585,
                                    If(friend[i] == 3, 480,
                                       If(friend[i] == 4, 540, 0))))
    available_end_expr = If(friend[i] == 0, 765,
                            If(friend[i] == 1, 1245,
                               If(friend[i] == 2, 1275,
                                  If(friend[i] == 3, 1230,
                                     If(friend[i] == 4, 1065, 0))))

    # Add constraints if this step is used
    solver.add(Implies(used[i], start_time[i] >= arrival_time))
    solver.add(Implies(used[i], start_time[i] >= available_start_expr))
    solver.add(Implies(used[i], end_time[i] == start_time[i] + 90))
    solver.add(Implies(used[i], end_time[i] <= available_end_expr))

# Maximize the number of used steps
objective = Sum([If(used[i], 1, 0) for i in range(MAX_STEPS)])
solver.maximize(objective)

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(MAX_STEPS):
        if is_true(model.eval(used[i])):
            f = model.eval(friend[i]).as_long()
            st = model.eval(start_time[i]).as_long()
            et = model.eval(end_time[i]).as_long()
            name = friends_info[f]['name']
            def to_time_str(m):
                h = m // 60
                m = m % 60
                return f"{h}:{m:02d}"
            itinerary.append({
                "action": "meet",
                "location": friends_info[f]['location'],
                "person": name,
                "start_time": to_time_str(st),
                "end_time": to_time_str(et)
            })
    # Sort by start time
    itinerary.sort(key=lambda x: x['start_time'])
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"itinerary": []}))