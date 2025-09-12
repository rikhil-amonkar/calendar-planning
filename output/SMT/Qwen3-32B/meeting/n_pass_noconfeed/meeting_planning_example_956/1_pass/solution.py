from z3 import *
import json

# Define locations
locations = [
    "The Castro",
    "Alamo Square",
    "Richmond District",
    "Financial District",
    "Union Square",
    "Fisherman's Wharf",
    "Marina District",
    "Haight-Ashbury",
    "Mission District",
    "Pacific Heights",
    "Golden Gate Park"
]

# Define travel times between locations (in minutes)
travel_time = [
    [0, 8, 16, 21, 19, 24, 21, 6, 7, 16, 13],
    [8, 0, 11, 17, 14, 19, 15, 5, 10, 10, 9],
    [16, 13, 0, 22, 21, 18, 9, 10, 20, 10, 9],
    [20, 17, 21, 0, 9, 10, 15, 19, 17, 13, 23],
    [17, 15, 20, 9, 0, 15, 18, 18, 14, 15, 22],
    [27, 21, 18, 11, 13, 0, 9, 22, 22, 12, 25],
    [22, 15, 11, 17, 16, 10, 0, 16, 20, 7, 18],
    [6, 5, 10, 21, 19, 23, 17, 0, 12, 11, 7],
    [7, 11, 20, 15, 15, 22, 19, 12, 0, 16, 17],
    [16, 10, 12, 13, 12, 13, 6, 11, 15, 0, 15],
    [13, 9, 7, 26, 22, 24, 16, 7, 17, 16, 0]
]

# Define friends
friends = [
    {
        "name": "William",
        "location": 1,  # Alamo Square
        "available_start": 14 * 60 + 15,  # 855
        "available_end": 17 * 60 + 15,    # 1035
        "min_duration": 60
    },
    {
        "name": "Joshua",
        "location": 2,  # Richmond District
        "available_start": 7 * 60,        # 420
        "available_end": 20 * 60,         # 1200
        "min_duration": 15
    },
    {
        "name": "Joseph",
        "location": 3,  # Financial District
        "available_start": 11 * 60 + 15,  # 675
        "available_end": 13 * 60 + 30,    # 810
        "min_duration": 15
    },
    {
        "name": "David",
        "location": 4,  # Union Square
        "available_start": 16 * 60 + 45,  # 1005
        "available_end": 19 * 60 + 15,    # 1155
        "min_duration": 45
    },
    {
        "name": "Brian",
        "location": 5,  # Fisherman's Wharf
        "available_start": 13 * 60 + 45,  # 825
        "available_end": 20 * 60 + 45,    # 1245
        "min_duration": 105
    },
    {
        "name": "Karen",
        "location": 6,  # Marina District
        "available_start": 11 * 60 + 30,  # 690
        "available_end": 18 * 60 + 30,    # 1110
        "min_duration": 15
    },
    {
        "name": "Anthony",
        "location": 7,  # Haight-Ashbury
        "available_start": 7 * 60 + 15,   # 435
        "available_end": 10 * 60 + 30,    # 630
        "min_duration": 30
    },
    {
        "name": "Matthew",
        "location": 8,  # Mission District
        "available_start": 17 * 60 + 15,  # 1035
        "available_end": 19 * 60 + 15,    # 1155
        "min_duration": 120
    },
    {
        "name": "Helen",
        "location": 9,  # Pacific Heights
        "available_start": 8 * 60,        # 480
        "available_end": 12 * 60,         # 720
        "min_duration": 75
    },
    {
        "name": "Jeffrey",
        "location": 10,  # Golden Gate Park
        "available_start": 19 * 60,       # 1140
        "available_end": 21 * 60 + 30,    # 1290
        "min_duration": 60
    }
]

max_steps = 10  # 10 friends
solver = Solver()

# Create variables for each step
friend = [Int(f'friend_{i}') for i in range(max_steps)]
start_time = [Int(f'start_time_{i}') for i in range(max_steps)]
end_time = [Int(f'end_time_{i}') for i in range(max_steps)]
is_used = [Bool(f'is_used_{i}') for i in range(max_steps)]
location = [Int(f'location_{i}') for i in range(max_steps)]

current_time = [Int(f'current_time_{i}') for i in range(max_steps)]
current_location = [Int(f'current_location_{i}') for i in range(max_steps)]

# Add constraints for each step
for i in range(max_steps):
    # If is_used[i], then friend[i] is between 0 and 9
    solver.add(Implies(is_used[i], And(friend[i] >= 0, friend[i] <= 9)))
    
    # location[i] is the location of the friend
    solver.add(Implies(is_used[i], location[i] == friends[friend[i]]["location"]))
    
    # start_time[i] >= available_start of the friend
    solver.add(Implies(is_used[i], start_time[i] >= friends[friend[i]]["available_start"]))
    
    # end_time[i] >= start_time[i] + min_duration
    solver.add(Implies(is_used[i], end_time[i] >= start_time[i] + friends[friend[i]]["min_duration"]))
    
    # end_time[i] <= available_end of the friend
    solver.add(Implies(is_used[i], end_time[i] <= friends[friend[i]]["available_end"]))
    
    # current_time and current_location for this step
    if i == 0:
        # First step
        solver.add(current_time[i] == If(is_used[i], end_time[i], 540))  # 9:00 AM
        solver.add(current_location[i] == If(is_used[i], location[i], 0))  # The Castro
        # start_time constraint
        solver.add(Implies(is_used[i], start_time[i] >= 540 + travel_time[0][location[i]]))
    else:
        # Subsequent steps
        solver.add(current_time[i] == If(is_used[i], end_time[i], current_time[i-1]))
        solver.add(current_location[i] == If(is_used[i], location[i], current_location[i-1]))
        
        # Generate travel_time_expr between current_location[i-1] and location[i]
        prev_loc = current_location[i-1]
        curr_loc = location[i]
        travel_time_expr = 0
        for p in range(11):
            for c in range(11):
                cond = And(prev_loc == p, curr_loc == c)
                travel_time_expr = If(cond, travel_time[p][c], travel_time_expr)
        solver.add(Implies(is_used[i], start_time[i] >= current_time[i-1] + travel_time_expr))

# Calculate total friends met
total_friends = Sum([If(is_used[i], 1, 0) for i in range(max_steps)])

# Find the maximum number of friends that can be met
best_model = None
max_k = 10
found = False

for k in range(max_k, 0, -1):
    s = Solver()
    for c in solver.assertions():
        s.add(c)
    s.add(total_friends == k)
    if s.check() == sat:
        found = True
        best_model = s.model()
        break

if not found:
    s = Solver()
    for c in solver.assertions():
        s.add(c)
    s.add(total_friends == 0)
    if s.check() == sat:
        best_model = s.model()
    else:
        print(json.dumps({"itinerary": []}))
        exit()

# Extract the itinerary
itinerary = []
for i in range(max_steps):
    if best_model.evaluate(is_used[i]):
        friend_idx = best_model[friend[i]].as_long()
        start = best_model[start_time[i]].as_long()
        end = best_model[end_time[i]].as_long()
        name = friends[friend_idx]["name"]
        loc_idx = friends[friend_idx]["location"]
        loc_name = locations[loc_idx]
        # Convert time to H:MM format
        def to_time_str(t):
            h = t // 60
            m = t % 60
            return f"{h}:{m:02d}"
        start_str = to_time_str(start)
        end_str = to_time_str(end)
        itinerary.append({
            "action": "meet",
            "location": loc_name,
            "person": name,
            "start_time": start_str,
            "end_time": end_str
        })

# Output JSON
print(json.dumps({"itinerary": itinerary}, indent=2))