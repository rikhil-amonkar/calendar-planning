from z3 import *
import json

def m_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

friends = [
    {'name': 'Mark', 'loc': 6, 'start': 600, 'end': 1275, 'min_dur': 75},
    {'name': 'William', 'loc': 4, 'start': 795, 'end': 1170, 'min_dur': 30},
    {'name': 'Robert', 'loc': 5, 'start': 855, 'end': 1290, 'min_dur': 45},
    {'name': 'Linda', 'loc': 2, 'start': 930, 'end': 1185, 'min_dur': 30},
    {'name': 'Elizabeth', 'loc': 3, 'start': 1035, 'end': 1170, 'min_dur': 105},
    {'name': 'Rebecca', 'loc': 1, 'start': 1095, 'end': 1245, 'min_dur': 60},
]

travel_times = [
    [0, 20, 17, 6, 7, 11, 18],
    [21, 0, 15, 15, 26, 12, 14],
    [17, 16, 0, 15, 24, 11, 24],
    [6, 15, 15, 0, 11, 7, 17],
    [7, 25, 24, 12, 0, 17, 15],
    [13, 11, 10, 7, 17, 0, 19],
    [21, 14, 23, 17, 16, 21, 0],
]

location_names = [
    "The Castro",
    "Presidio",
    "Sunset District",
    "Haight-Ashbury",
    "Mission District",
    "Golden Gate Park",
    "Russian Hill"
]

def get_friend_start(friend_idx_var):
    return If(friend_idx_var == 0, friends[0]['start'],
              If(friend_idx_var == 1, friends[1]['start'],
                 If(friend_idx_var == 2, friends[2]['start'],
                    If(friend_idx_var == 3, friends[3]['start'],
                       If(friend_idx_var == 4, friends[4]['start'],
                          friends[5]['start']))))

def get_friend_end(friend_idx_var):
    return If(friend_idx_var == 0, friends[0]['end'],
              If(friend_idx_var == 1, friends[1]['end'],
                 If(friend_idx_var == 2, friends[2]['end'],
                    If(friend_idx_var == 3, friends[3]['end'],
                       If(friend_idx_var == 4, friends[4]['end'],
                          friends[5]['end']))))

def get_friend_min(friend_idx_var):
    return If(friend_idx_var == 0, friends[0]['min_dur'],
              If(friend_idx_var == 1, friends[1]['min_dur'],
                 If(friend_idx_var == 2, friends[2]['min_dur'],
                    If(friend_idx_var == 3, friends[3]['min_dur'],
                       If(friend_idx_var == 4, friends[4]['min_dur'],
                          friends[5]['min_dur']))))

solver = Optimize()

num_steps = 6

is_met = [Bool(f'is_met_{i}') for i in range(num_steps)]
friend = [Int(f'friend_{i}') for i in range(num_steps)]
start = [Int(f'start_{i}') for i in range(num_steps)]
end = [Int(f'end_{i}') for i in range(num_steps)]
loc = [Int(f'loc_{i}') for i in range(num_steps)]

# Add constraints for friend indices and locations
for i in range(num_steps):
    solver.add(Implies(is_met[i], And(0 <= friend[i], friend[i] < len(friends))))
    solver.add(Implies(is_met[i], loc[i] == friends[friend[i]]['loc']))

# Ensure no duplicate friends
for i in range(num_steps):
    for j in range(i+1, num_steps):
        solver.add(Implies(And(is_met[i], is_met[j]), friend[i] != friend[j]))

# Track previous end and location for each step
prev_end_vars = [Int(f'prev_end_{i}') for i in range(num_steps + 1)]
prev_loc_vars = [Int(f'prev_loc_{i}') for i in range(num_steps + 1)]

# Initialize initial time and location
solver.add(prev_end_vars[0] == 540)  # 9:00 AM
solver.add(prev_loc_vars[0] == 0)    # The Castro

for i in range(num_steps):
    # Get friend data for this step
    f_start = get_friend_start(friend[i])
    f_end = get_friend_end(friend[i])
    f_min = get_friend_min(friend[i])

    # Constraints for this step
    solver.add(Implies(is_met[i], start[i] >= prev_end_vars[i] + travel_times[prev_loc_vars[i]][loc[i]]))
    solver.add(Implies(is_met[i], start[i] >= f_start))
    solver.add(Implies(is_met[i], end[i] <= f_end))
    solver.add(Implies(is_met[i], end[i] - start[i] >= f_min))
    solver.add(Implies(is_met[i], end[i] >= start[i]))

    # Update previous end and location for next step
    solver.add(prev_end_vars[i+1] == If(is_met[i], end[i], prev_end_vars[i]))
    solver.add(prev_loc_vars[i+1] == If(is_met[i], loc[i], prev_loc_vars[i]))

# Maximize the number of friends met
total_friends = Sum([If(is_met[i], 1, 0) for i in range(num_steps)])
solver.maximize(total_friends)

# Check if the problem is satisfiable
if solver.check() == sat:
    model = solver.model()
    # Collect the meetings
    itinerary = []
    for i in range(num_steps):
        if is_true(model.eval(is_met[i])):
            # This step is a meeting
            friend_idx = model.eval(friend[i]).as_long()
            start_m = model.eval(start[i]).as_long()
            end_m = model.eval(end[i]).as_long()
            loc_code = model.eval(loc[i]).as_long()
            friend_name = friends[friend_idx]['name']
            location_name = location_names[loc_code]
            # Convert times
            start_time = m_to_time(start_m)
            end_time = m_to_time(end_m)
            itinerary.append({
                "action": "meet",
                "location": location_name,
                "person": friend_name,
                "start_time": start_time,
                "end_time": end_time
            })
    # Output JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")