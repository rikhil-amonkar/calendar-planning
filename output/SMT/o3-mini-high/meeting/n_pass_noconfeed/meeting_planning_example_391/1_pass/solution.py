from z3 import *
import json

# Travel times in minutes for each route between locations
travel = {
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Russian Hill"): 24,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Financial District"): 30,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "Presidio"): 18,
    ("Alamo Square", "Financial District"): 17,
    ("Russian Hill", "Sunset District"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "Presidio"): 14,
    ("Russian Hill", "Financial District"): 11,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Alamo Square"): 18,
    ("Presidio", "Russian Hill"): 14,
    ("Presidio", "Financial District"): 23,
    ("Financial District", "Sunset District"): 31,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Presidio"): 22
}

# Define the friends with their meeting locations, availability windows (in minutes after midnight),
# and minimum required meeting durations (in minutes)
# Times: 8:15 = 495, 8:45 = 525, 9:00 = 540, 12:30 = 750, 18:30 = 1110, 19:00 = 1140,
# 19:15 = 1155, 21:30 = 1290, 21:45 = 1305.
friends = [
    {"name": "Kevin", "location": "Alamo Square", "avail_start": 495, "avail_end": 1290, "min_dur": 75},
    {"name": "Kimberly", "location": "Russian Hill", "avail_start": 525, "avail_end": 750, "min_dur": 30},
    {"name": "Joseph", "location": "Presidio", "avail_start": 1110, "avail_end": 1155, "min_dur": 45},
    {"name": "Thomas", "location": "Financial District", "avail_start": 1140, "avail_end": 1305, "min_dur": 45}
]

# Starting point: You arrive at Sunset District at 9:00 AM (540 minutes after midnight)
start_location = "Sunset District"
arrival_time = 540

# Create an Optimize object to maximize the number of meetings
opt = Optimize()

num_friends = len(friends)
# Decision variables for each meeting:
# s_i: start time of meeting with friend i
# e_i: end time of meeting with friend i
# attend_i: Boolean, whether to attend friend i's meeting
s_vars = [Int(f"s_{i}") for i in range(num_friends)]
e_vars = [Int(f"e_{i}") for i in range(num_friends)]
attend = [Bool(f"attend_{i}") for i in range(num_friends)]

# Add constraints for each friend's meeting if it is attended.
for i, friend in enumerate(friends):
    # Travel time from starting location to the friend's location.
    travel_from_start = travel[(start_location, friend["location"])]
    # If attending, the meeting cannot start before you arrive at that location.
    opt.add(Implies(attend[i], s_vars[i] >= arrival_time + travel_from_start))
    # Must respect the friend's availability window.
    opt.add(Implies(attend[i], s_vars[i] >= friend["avail_start"]))
    opt.add(Implies(attend[i], e_vars[i] <= friend["avail_end"]))
    # Meeting duration must be at least the minimum required.
    opt.add(Implies(attend[i], e_vars[i] - s_vars[i] >= friend["min_dur"]))
    # Special constraint for Joseph: his available window is exactly 45 minutes.
    if friend["name"] == "Joseph":
        opt.add(Implies(attend[i], s_vars[i] == 1110))
        opt.add(Implies(attend[i], e_vars[i] == 1155))

# Add ordering constraints for every pair of attended meetings.
# If both meetings i and j are attended, then either meeting i happens before meeting j
# (accounting for travel time from i to j) or vice-versa.
for i in range(num_friends):
    for j in range(i + 1, num_friends):
        loc_i = friends[i]["location"]
        loc_j = friends[j]["location"]
        travel_i_j = travel[(loc_i, loc_j)]
        travel_j_i = travel[(loc_j, loc_i)]
        opt.add(Implies(And(attend[i], attend[j]),
                        Or(e_vars[i] + travel_i_j <= s_vars[j],
                           e_vars[j] + travel_j_i <= s_vars[i])))

# Objective: maximize the total number of meetings attended.
total_attended = Sum([If(attend[i], 1, 0) for i in range(num_friends)])
opt.maximize(total_attended)

# Solve the optimization problem.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    # Collect the meetings that are attended
    for i in range(num_friends):
        if is_true(model.evaluate(attend[i])):
            s_val = model.evaluate(s_vars[i]).as_long()
            e_val = model.evaluate(e_vars[i]).as_long()
            schedule.append((s_val, {
                "action": "meet",
                "location": friends[i]["location"],
                "person": friends[i]["name"],
                "start_time": s_val,  # will convert to formatted string below
                "end_time": e_val
            }))
    # Sort the scheduled meetings by start time.
    schedule.sort(key=lambda x: x[0])
    
    # Helper function to convert minutes after midnight to a "H:MM" string in 24-hour format.
    def format_time(minutes):
        hour = minutes // 60
        minute = minutes % 60
        return f"{hour}:{minute:02d}"
    
    itinerary = []
    for _, event in schedule:
        event["start_time"] = format_time(event["start_time"])
        event["end_time"] = format_time(event["end_time"])
        itinerary.append(event)
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    # If no feasible schedule is found, output an empty itinerary.
    print(json.dumps({"itinerary": []}))