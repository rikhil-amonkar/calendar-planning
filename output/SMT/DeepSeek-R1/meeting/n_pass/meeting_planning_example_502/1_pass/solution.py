import json
from z3 import *

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

# Define travel times between locations
travel_times = {
    "Financial District": {
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Union Square": 9,
        "Fisherman's Wharf": 10,
        "Pacific Heights": 13,
        "North Beach": 7
    },
    "Golden Gate Park": {
        "Financial District": 26,
        "Chinatown": 23,
        "Union Square": 22,
        "Fisherman's Wharf": 24,
        "Pacific Heights": 16,
        "North Beach": 24
    },
    "Chinatown": {
        "Financial District": 5,
        "Golden Gate Park": 23,
        "Union Square": 7,
        "Fisherman's Wharf": 8,
        "Pacific Heights": 10,
        "North Beach": 3
    },
    "Union Square": {
        "Financial District": 9,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Fisherman's Wharf": 15,
        "Pacific Heights": 15,
        "North Beach": 10
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Union Square": 13,
        "Pacific Heights": 12,
        "North Beach": 6
    },
    "Pacific Heights": {
        "Financial District": 13,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Union Square": 12,
        "Fisherman's Wharf": 13,
        "North Beach": 9
    },
    "North Beach": {
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Chinatown": 6,
        "Union Square": 7,
        "Fisherman's Wharf": 5,
        "Pacific Heights": 8
    }
}

friends = {
    "Rebecca": {
        "location": "Fisherman's Wharf",
        "start_available": "8:00",
        "end_available": "11:15",
        "min_duration": 30
    },
    "Joseph": {
        "location": "Pacific Heights",
        "start_available": "8:15",
        "end_available": "9:30",
        "min_duration": 60
    },
    "Stephanie": {
        "location": "Golden Gate Park",
        "start_available": "11:00",
        "end_available": "15:00",
        "min_duration": 105
    },
    "Karen": {
        "location": "Chinatown",
        "start_available": "13:45",
        "end_available": "16:30",
        "min_duration": 15
    },
    "Brian": {
        "location": "Union Square",
        "start_available": "15:00",
        "end_available": "17:15",
        "min_duration": 30
    },
    "Steven": {
        "location": "North Beach",
        "start_available": "14:30",
        "end_available": "20:45",
        "min_duration": 120
    }
}

# Convert time strings to minutes
for friend, data in friends.items():
    data['start_min'] = time_to_minutes(data['start_available'])
    data['end_min'] = time_to_minutes(data['end_available'])

# Create Z3 variables
meet = {}
start = {}
for friend in friends:
    meet[friend] = Bool(f"meet_{friend}")
    start[friend] = Int(f"start_{friend}")

# Set up the solver with optimization
opt = Optimize()

# Constraints for each friend
for friend, data in friends.items():
    # If meeting, it must be within the available window
    opt.add(Implies(meet[friend], start[friend] >= data['start_min']))
    opt.add(Implies(meet[friend], start[friend] + data['min_duration'] <= data['end_min']))
    # Travel from Financial District to the friend's location
    travel_time = travel_times["Financial District"][data['location']]
    opt.add(Implies(meet[friend], start[friend] >= 540 + travel_time))  # 540 minutes = 9:00 AM

# Constraints for every pair of distinct friends
friend_names = list(friends.keys())
for i in range(len(friend_names)):
    for j in range(i+1, len(friend_names)):
        friend_i = friend_names[i]
        friend_j = friend_names[j]
        loc_i = friends[friend_i]['location']
        loc_j = friends[friend_j]['location']
        dur_i = friends[friend_i]['min_duration']
        dur_j = friends[friend_j]['min_duration']
        travel_ij = travel_times[loc_i][loc_j]
        travel_ji = travel_times[loc_j][loc_i]
        opt.add(Implies(And(meet[friend_i], meet[friend_j]),
                         Or(
                             start[friend_i] + dur_i + travel_ij <= start[friend_j],
                             start[friend_j] + dur_j + travel_ji <= start[friend_i]
                         )))

# Objective: maximize the number of meetings
objective = Sum([If(meet[friend], 1, 0) for friend in friends])
opt.maximize(objective)

# Solve and output
if opt.check() == sat:
    model = opt.model()
    schedule = []
    for friend in friends:
        if is_true(model[meet[friend]]):
            s_val = model[start[friend]].as_long()
            dur = friends[friend]['min_duration']
            start_time = minutes_to_time(s_val)
            end_time = minutes_to_time(s_val + dur)
            schedule.append({
                "action": "meet",
                "person": friend,
                "start_time": start_time,
                "end_time": end_time
            })
    schedule.sort(key=lambda x: x['start_time'])
    result = {"itinerary": schedule}
    print("SOLUTION:")
    print(json.dumps(result))
else:
    print("No solution found")