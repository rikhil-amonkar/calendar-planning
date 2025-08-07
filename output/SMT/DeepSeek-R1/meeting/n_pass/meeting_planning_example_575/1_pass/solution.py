import json
from z3 import *

# Define travel_time dictionary
travel_time = {
    "The Castro": {
        "Presidio": 20,
        "Sunset District": 17,
        "Haight-Ashbury": 6,
        "Mission District": 7,
        "Golden Gate Park": 11,
        "Russian Hill": 18
    },
    "Presidio": {
        "The Castro": 21,
        "Sunset District": 15,
        "Haight-Ashbury": 15,
        "Mission District": 26,
        "Golden Gate Park": 12,
        "Russian Hill": 14
    },
    "Sunset District": {
        "The Castro": 17,
        "Presidio": 16,
        "Haight-Ashbury": 15,
        "Mission District": 24,
        "Golden Gate Park": 11,
        "Russian Hill": 24
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "Presidio": 15,
        "Sunset District": 15,
        "Mission District": 11,
        "Golden Gate Park": 7,
        "Russian Hill": 17
    },
    "Mission District": {
        "The Castro": 7,
        "Presidio": 25,
        "Sunset District": 24,
        "Haight-Ashbury": 12,
        "Golden Gate Park": 17,
        "Russian Hill": 15
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Presidio": 11,
        "Sunset District": 10,
        "Haight-Ashbury": 7,
        "Mission District": 17,
        "Russian Hill": 19
    },
    "Russian Hill": {
        "The Castro": 21,
        "Presidio": 14,
        "Sunset District": 23,
        "Haight-Ashbury": 17,
        "Mission District": 16,
        "Golden Gate Park": 21
    }
}

# Define friends data: (name, location, availability_start (min), availability_end (min), min_duration (min))
friends = [
    ("Rebecca", "Presidio", 18*60+15, 20*60+45, 60),
    ("Linda", "Sunset District", 15*60+30, 19*60+45, 30),
    ("Elizabeth", "Haight-Ashbury", 17*60+15, 19*60+30, 105),
    ("William", "Mission District", 13*60+15, 19*60+30, 30),
    ("Robert", "Golden Gate Park", 14*60+15, 21*60+30, 45),
    ("Mark", "Russian Hill", 10*60+0, 21*60+15, 75)
]

# Create Z3 solver and optimizer
opt = Optimize()
n = len(friends)

# Decision variables: whether we meet each friend, and start time of meeting
m = [Bool(f'm_{i}') for i in range(n)]
start = [Int(f'start_{i}') for i in range(n)]

# Add constraints for each friend
for i in range(n):
    name, loc, avail_start, avail_end, dur = friends[i]
    # If meeting friend i, then start time must be within availability window
    opt.add(Implies(m[i], And(start[i] >= avail_start, start[i] + dur <= avail_end)))
    # Travel time from The Castro to friend's location
    travel_from_start = travel_time["The Castro"][loc]
    opt.add(Implies(m[i], start[i] >= 9*60 + travel_from_start))

# Add pairwise constraints for every two different friends
for i in range(n):
    for j in range(i+1, n):
        if i != j:
            name_i, loc_i, avail_start_i, avail_end_i, dur_i = friends[i]
            name_j, loc_j, avail_start_j, avail_end_j, dur_j = friends[j]
            t_ij = travel_time[loc_i][loc_j]
            t_ji = travel_time[loc_j][loc_i]
            end_i = start[i] + dur_i
            end_j = start[j] + dur_j
            # If both meetings are scheduled, enforce travel time constraint
            opt.add(Implies(And(m[i], m[j]), 
                          Or(end_i + t_ij <= start[j], 
                             end_j + t_ji <= start[i])))

# Objective: maximize the number of friends met
opt.maximize(Sum([If(m[i], 1, 0) for i in range(n)]))

# Check for a solution
if opt.check() == sat:
    model = opt.model()
    # Collect scheduled meetings
    scheduled_meetings = []
    for i in range(n):
        if model.evaluate(m[i]):
            name, loc, avail_start, avail_end, dur = friends[i]
            start_val = model.evaluate(start[i]).as_long()
            end_val = start_val + dur
            # Format start and end times
            start_time_str = f"{start_val // 60:02d}:{start_val % 60:02d}"
            end_time_str = f"{end_val // 60:02d}:{end_val % 60:02d}"
            scheduled_meetings.append((name, start_time_str, end_time_str))
    # Sort meetings by start time
    scheduled_meetings.sort(key=lambda x: (int(x[1].split(':')[0]), int(x[1].split(':')[1])))
    # Format as JSON
    itinerary = [{"action": "meet", "person": name, "start_time": start, "end_time": end} 
                 for name, start, end in scheduled_meetings]
    print("SOLUTION:")
    print(json.dumps({"itinerary": itinerary}))
else:
    print("SOLUTION:")
    print(json.dumps({"itinerary": []}))