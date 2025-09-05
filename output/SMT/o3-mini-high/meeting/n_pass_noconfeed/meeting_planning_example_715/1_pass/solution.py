from z3 import *
import json

def minutes_to_time_str(m):
    h = m // 60
    mi = m % 60
    return f"{h}:{mi:02d}"

# Friend meeting data (times in minutes after midnight)
# Times: e.g., 9:00 -> 540, 9:30 -> 570, 10:15 -> 615, 11:15 -> 675, etc.
friend_data = [
    {"name": "Amanda", "location": "Marina District", "start": 885, "end": 1170, "duration": 105},       # 14:45-19:30, min 105
    {"name": "Melissa", "location": "The Castro", "start": 570, "end": 1020, "duration": 30},             # 9:30-17:00, min 30
    {"name": "Jeffrey", "location": "Fisherman's Wharf", "start": 765, "end": 1125, "duration": 120},     # 12:45-18:45, min 120
    {"name": "Matthew", "location": "Bayview", "start": 615, "end": 795, "duration": 30},                 # 10:15-13:15, min 30
    {"name": "Nancy", "location": "Pacific Heights", "start": 1020, "end": 1290, "duration": 105},        # 17:00-21:30, min 105
    {"name": "Karen", "location": "Mission District", "start": 1050, "end": 1230, "duration": 105},       # 17:30-20:30, min 105
    {"name": "Robert", "location": "Alamo Square", "start": 675, "end": 1050, "duration": 120},           # 11:15-17:30, min 120
    {"name": "Joseph", "location": "Golden Gate Park", "start": 510, "end": 1275, "duration": 105}        # 8:30-21:15, min 105
]

# Dummy meeting for starting point at Presidio at 9:00 (540)
dummy = {"name": "Start", "location": "Presidio", "start": 540, "duration": 0}

# Travel time matrix (in minutes) for the relevant locations.
travel_times = {
    ("Presidio", "Marina District"): 11,
    ("Presidio", "The Castro"): 21,
    ("Presidio", "Fisherman's Wharf"): 19,
    ("Presidio", "Bayview"): 31,
    ("Presidio", "Pacific Heights"): 11,
    ("Presidio", "Mission District"): 26,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Golden Gate Park"): 12,
    
    ("Marina District", "Presidio"): 10,
    ("Marina District", "The Castro"): 22,
    ("Marina District", "Fisherman's Wharf"): 10,
    ("Marina District", "Bayview"): 27,
    ("Marina District", "Pacific Heights"): 7,
    ("Marina District", "Mission District"): 20,
    ("Marina District", "Alamo Square"): 15,
    ("Marina District", "Golden Gate Park"): 18,
    
    ("The Castro", "Presidio"): 20,
    ("The Castro", "Marina District"): 21,
    ("The Castro", "Fisherman's Wharf"): 24,
    ("The Castro", "Bayview"): 19,
    ("The Castro", "Pacific Heights"): 16,
    ("The Castro", "Mission District"): 7,
    ("The Castro", "Alamo Square"): 8,
    ("The Castro", "Golden Gate Park"): 11,
    
    ("Fisherman's Wharf", "Presidio"): 17,
    ("Fisherman's Wharf", "Marina District"): 9,
    ("Fisherman's Wharf", "The Castro"): 27,
    ("Fisherman's Wharf", "Bayview"): 26,
    ("Fisherman's Wharf", "Pacific Heights"): 12,
    ("Fisherman's Wharf", "Mission District"): 22,
    ("Fisherman's Wharf", "Alamo Square"): 21,
    ("Fisherman's Wharf", "Golden Gate Park"): 25,
    
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Marina District"): 27,
    ("Bayview", "The Castro"): 19,
    ("Bayview", "Fisherman's Wharf"): 25,
    ("Bayview", "Pacific Heights"): 23,
    ("Bayview", "Mission District"): 13,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Golden Gate Park"): 22,
    
    ("Pacific Heights", "Presidio"): 11,
    ("Pacific Heights", "Marina District"): 6,
    ("Pacific Heights", "The Castro"): 16,
    ("Pacific Heights", "Fisherman's Wharf"): 13,
    ("Pacific Heights", "Bayview"): 22,
    ("Pacific Heights", "Mission District"): 15,
    ("Pacific Heights", "Alamo Square"): 10,
    ("Pacific Heights", "Golden Gate Park"): 15,
    
    ("Mission District", "Presidio"): 25,
    ("Mission District", "Marina District"): 19,
    ("Mission District", "The Castro"): 7,
    ("Mission District", "Fisherman's Wharf"): 22,
    ("Mission District", "Bayview"): 14,
    ("Mission District", "Pacific Heights"): 16,
    ("Mission District", "Alamo Square"): 11,
    ("Mission District", "Golden Gate Park"): 17,
    
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Marina District"): 15,
    ("Alamo Square", "The Castro"): 8,
    ("Alamo Square", "Fisherman's Wharf"): 19,
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Pacific Heights"): 10,
    ("Alamo Square", "Mission District"): 10,
    ("Alamo Square", "Golden Gate Park"): 9,
    
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Marina District"): 16,
    ("Golden Gate Park", "The Castro"): 13,
    ("Golden Gate Park", "Fisherman's Wharf"): 24,
    ("Golden Gate Park", "Bayview"): 23,
    ("Golden Gate Park", "Pacific Heights"): 16,
    ("Golden Gate Park", "Mission District"): 17,
    ("Golden Gate Park", "Alamo Square"): 9
}

# Create the Optimize solver
opt = Optimize()

n = len(friend_data)

# For each friend meeting, create a start time variable and a scheduled Boolean.
meeting_starts = [Int(f"start_{i}") for i in range(n)]
scheduled = [Bool(f"scheduled_{i}") for i in range(n)]

# Add constraints for each friend meeting
for i, friend in enumerate(friend_data):
    # If meeting is scheduled, it must start no earlier than the friend's available start
    opt.add(Implies(scheduled[i], meeting_starts[i] >= friend["start"]))
    # And finish by the available end time
    opt.add(Implies(scheduled[i], meeting_starts[i] + friend["duration"] <= friend["end"]))

# Enforce that each meeting (when scheduled) is reachable directly from the Presidio start
dummy_start = dummy["start"]  # 540
dummy_duration = dummy["duration"]  # 0
dummy_location = dummy["location"]  # "Presidio"
for i, friend in enumerate(friend_data):
    travel_from_dummy = travel_times[(dummy_location, friend["location"])]
    # If scheduled, must depart from Presidio at 9:00 and travel directly,
    # which enforces that if this meeting is the first visited, its start time is at least 540 + travel time.
    opt.add(Implies(scheduled[i], dummy_start + dummy_duration + travel_from_dummy <= meeting_starts[i]))

# For every pair of friend meetings, if both are scheduled, enforce non-overlap with travel time considerations.
# That is, for any two meetings, one must finish and then after travel the other may begin.
for i in range(n):
    for j in range(i+1, n):
        travel_ij = travel_times[(friend_data[i]["location"], friend_data[j]["location"])]
        travel_ji = travel_times[(friend_data[j]["location"], friend_data[i]["location"])]
        option1 = meeting_starts[i] + friend_data[i]["duration"] + travel_ij <= meeting_starts[j]
        option2 = meeting_starts[j] + friend_data[j]["duration"] + travel_ji <= meeting_starts[i]
        opt.add(Implies(And(scheduled[i], scheduled[j]), Or(option1, option2)))

# Objective: maximize the total number of meetings scheduled.
total_scheduled = Sum([If(scheduled[i], 1, 0) for i in range(n)])
opt.maximize(total_scheduled)

# Solve and extract the schedule.
if opt.check() == sat:
    model = opt.model()
    schedule = []
    # Collect scheduled meetings from the model.
    for i, friend in enumerate(friend_data):
        if is_true(model.evaluate(scheduled[i])):
            start_val = model.evaluate(meeting_starts[i]).as_long()
            end_val = start_val + friend["duration"]
            schedule.append({
                "person": friend["name"],
                "location": friend["location"],
                "start": start_val,
                "end": end_val
            })
    # Sort meetings by start time.
    schedule.sort(key=lambda x: x["start"])
    
    itinerary = []
    for meeting in schedule:
        itinerary.append({
            "action": "meet",
            "person": meeting["person"],
            "location": meeting["location"],
            "start_time": minutes_to_time_str(meeting["start"]),
            "end_time": minutes_to_time_str(meeting["end"])
        })
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print(json.dumps({"itinerary": []}))