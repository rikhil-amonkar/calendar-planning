import json
from z3 import *

# Convert time to minutes
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Convert minutes to time string
def minutes_to_time(minutes):
    hours = minutes // 60
    minutes %= 60
    return f"{hours:02d}:{minutes:02d}"

# Define locations
locations = {
    "Presidio": 0,
    "Pacific Heights": 1,
    "Golden Gate Park": 2,
    "Fisherman's Wharf": 3,
    "Marina District": 4,
    "Alamo Square": 5,
    "Sunset District": 6,
    "Nob Hill": 7,
    "North Beach": 8
}

# Travel time matrix (9x9)
travel_time = [
    [0, 11, 12, 19, 11, 19, 15, 18, 18],   # Presidio to others
    [11, 0, 15, 13, 6, 10, 21, 8, 9],       # Pacific Heights to others
    [11, 16, 0, 24, 16, 9, 10, 20, 23],     # Golden Gate Park to others
    [17, 12, 25, 0, 9, 21, 27, 11, 6],      # Fisherman's Wharf to others
    [10, 7, 18, 10, 0, 15, 19, 12, 11],     # Marina District to others
    [17, 10, 9, 19, 15, 0, 16, 11, 15],     # Alamo Square to others
    [16, 21, 11, 29, 21, 17, 0, 27, 28],    # Sunset District to others
    [17, 8, 17, 10, 11, 11, 24, 0, 8],      # Nob Hill to others
    [17, 8, 22, 5, 9, 16, 27, 7, 0]         # North Beach to others
]

# Friends data: name, location, start window, end window, min duration
friends_data = [
    {"name": "Michelle", "location": "Golden Gate Park", 
     "start_win": "20:00", "end_win": "21:00", "min_dur": 15},
    {"name": "Emily", "location": "Fisherman's Wharf", 
     "start_win": "16:15", "end_win": "19:00", "min_dur": 30},
    {"name": "Mark", "location": "Marina District", 
     "start_win": "18:15", "end_win": "19:45", "min_dur": 75},
    {"name": "Barbara", "location": "Alamo Square", 
     "start_win": "17:00", "end_win": "19:00", "min_dur": 120},
    {"name": "Laura", "location": "Sunset District", 
     "start_win": "19:00", "end_win": "21:15", "min_dur": 75},
    {"name": "Mary", "location": "Nob Hill", 
     "start_win": "17:30", "end_win": "19:00", "min_dur": 45},
    {"name": "Helen", "location": "North Beach", 
     "start_win": "11:00", "end_win": "12:15", "min_dur": 45}
]

# Convert friend data to minutes and location indices
for friend in friends_data:
    friend["start_win_min"] = time_to_minutes(friend["start_win"])
    friend["end_win_min"] = time_to_minutes(friend["end_win"])
    friend["loc_index"] = locations[friend["location"]]

# Start time at Presidio (9:00 AM in minutes)
start_time = time_to_minutes("9:00")

# Create Z3 solver
opt = Optimize()

# Create variables for each friend
n = len(friends_data)
meet = [Bool(f"meet_{i}") for i in range(n)]
t_start = [Int(f"t_start_{i}") for i in range(n)]

# Add constraints for each friend
for i, friend in enumerate(friends_data):
    # If we meet the friend, the meeting must be within their window and duration
    opt.add(Implies(meet[i], 
                   And(t_start[i] >= friend["start_win_min"],
                       t_start[i] + friend["min_dur"] <= friend["end_win_min"])))
    # The meeting must start after traveling from Presidio to the friend's location
    travel_from_start = travel_time[0][friend["loc_index"]]
    opt.add(Implies(meet[i], t_start[i] >= start_time + travel_from_start))

# Add disjunctive constraints for every pair of friends
for i in range(n):
    for j in range(i + 1, n):
        if i != j:
            # Travel time from friend i to j and j to i
            travel_i_j = travel_time[friends_data[i]["loc_index"]][friends_data[j]["loc_index"]]
            travel_j_i = travel_time[friends_data[j]["loc_index"]][friends_data[i]["loc_index"]]
            # Constraint: if both are met, then either i before j or j before i
            opt.add(Implies(And(meet[i], meet[j]),
                           Or(t_start[j] >= t_start[i] + friends_data[i]["min_dur"] + travel_i_j,
                              t_start[i] >= t_start[j] + friends_data[j]["min_dur"] + travel_j_i)))

# Maximize the number of meetings
num_meetings = Sum([If(meet[i], 1, 0) for i in range(n)])
opt.maximize(num_meetings)

# Solve the problem
if opt.check() == sat:
    m = opt.model()
    itinerary = []
    for i, friend in enumerate(friends_data):
        if m.evaluate(meet[i]):
            start_val = m.evaluate(t_start[i]).as_long()
            start_time_str = minutes_to_time(start_val)
            end_time_str = minutes_to_time(start_val + friend["min_dur"])
            itinerary.append({
                "action": "meet",
                "person": friend["name"],
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    # Output the itinerary in JSON format
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print('{"itinerary": []}')