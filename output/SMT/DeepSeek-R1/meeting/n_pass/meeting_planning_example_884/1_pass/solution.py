from z3 import *
import json

# Define travel times between locations
travel_dict = {
    ("Richmond District", "Chinatown"): 20,
    ("Richmond District", "Sunset District"): 11,
    ("Richmond District", "Alamo Square"): 13,
    ("Richmond District", "Financial District"): 22,
    ("Richmond District", "North Beach"): 17,
    ("Richmond District", "Embarcadero"): 19,
    ("Richmond District", "Presidio"): 7,
    ("Richmond District", "Golden Gate Park"): 9,
    ("Richmond District", "Bayview"): 27,
    ("Chinatown", "Richmond District"): 20,
    ("Chinatown", "Sunset District"): 29,
    ("Chinatown", "Alamo Square"): 17,
    ("Chinatown", "Financial District"): 5,
    ("Chinatown", "North Beach"): 3,
    ("Chinatown", "Embarcadero"): 5,
    ("Chinatown", "Presidio"): 19,
    ("Chinatown", "Golden Gate Park"): 23,
    ("Chinatown", "Bayview"): 20,
    ("Sunset District", "Richmond District"): 12,
    ("Sunset District", "Chinatown"): 30,
    ("Sunset District", "Alamo Square"): 17,
    ("Sunset District", "Financial District"): 30,
    ("Sunset District", "North Beach"): 28,
    ("Sunset District", "Embarcadero"): 30,
    ("Sunset District", "Presidio"): 16,
    ("Sunset District", "Golden Gate Park"): 11,
    ("Sunset District", "Bayview"): 22,
    ("Alamo Square", "Richmond District"): 11,
    ("Alamo Square", "Chinatown"): 15,
    ("Alamo Square", "Sunset District"): 16,
    ("Alamo Square", "Financial District"): 17,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Embarcadero"): 16,
    ("Alamo Square", "Presidio"): 17,
    ("Alamo Square", "Golden Gate Park"): 9,
    ("Alamo Square", "Bayview"): 16,
    ("Financial District", "Richmond District"): 21,
    ("Financial District", "Chinatown"): 5,
    ("Financial District", "Sunset District"): 30,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "North Beach"): 7,
    ("Financial District", "Embarcadero"): 4,
    ("Financial District", "Presidio"): 22,
    ("Financial District", "Golden Gate Park"): 23,
    ("Financial District", "Bayview"): 19,
    ("North Beach", "Richmond District"): 18,
    ("North Beach", "Chinatown"): 6,
    ("North Beach", "Sunset District"): 27,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Financial District"): 8,
    ("North Beach", "Embarcadero"): 6,
    ("North Beach", "Presidio"): 17,
    ("North Beach", "Golden Gate Park"): 22,
    ("North Beach", "Bayview"): 25,
    ("Embarcadero", "Richmond District"): 21,
    ("Embarcadero", "Chinatown"): 7,
    ("Embarcadero", "Sunset District"): 30,
    ("Embarcadero", "Alamo Square"): 19,
    ("Embarcadero", "Financial District"): 5,
    ("Embarcadero", "North Beach"): 5,
    ("Embarcadero", "Presidio"): 20,
    ("Embarcadero", "Golden Gate Park"): 25,
    ("Embarcadero", "Bayview"): 21,
    ("Presidio", "Richmond District"): 7,
    ("Presidio", "Chinatown"): 21,
    ("Presidio", "Sunset District"): 15,
    ("Presidio", "Alamo Square"): 19,
    ("Presidio", "Financial District"): 23,
    ("Presidio", "North Beach"): 18,
    ("Presidio", "Embarcadero"): 20,
    ("Presidio", "Golden Gate Park"): 12,
    ("Presidio", "Bayview"): 31,
    ("Golden Gate Park", "Richmond District"): 7,
    ("Golden Gate Park", "Chinatown"): 23,
    ("Golden Gate Park", "Sunset District"): 10,
    ("Golden Gate Park", "Alamo Square"): 9,
    ("Golden Gate Park", "Financial District"): 26,
    ("Golden Gate Park", "North Beach"): 23,
    ("Golden Gate Park", "Embarcadero"): 25,
    ("Golden Gate Park", "Presidio"): 11,
    ("Golden Gate Park", "Bayview"): 23,
    ("Bayview", "Richmond District"): 25,
    ("Bayview", "Chinatown"): 19,
    ("Bayview", "Sunset District"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "Financial District"): 19,
    ("Bayview", "North Beach"): 22,
    ("Bayview", "Embarcadero"): 19,
    ("Bayview", "Presidio"): 32,
    ("Bayview", "Golden Gate Park"): 22
}

# Define friends' data
friends_data = [
    {"name": "Robert", "location": "Chinatown", "window_start": 465, "window_end": 1050, "min_duration": 120},
    {"name": "David", "location": "Sunset District", "window_start": 750, "window_end": 1185, "min_duration": 45},
    {"name": "Matthew", "location": "Alamo Square", "window_start": 525, "window_end": 825, "min_duration": 90},
    {"name": "Jessica", "location": "Financial District", "window_start": 570, "window_end": 1125, "min_duration": 45},
    {"name": "Melissa", "location": "North Beach", "window_start": 435, "window_end": 1005, "min_duration": 45},
    {"name": "Mark", "location": "Embarcadero", "window_start": 915, "window_end": 1020, "min_duration": 45},
    {"name": "Deborah", "location": "Presidio", "window_start": 1140, "window_end": 1185, "min_duration": 45},
    {"name": "Karen", "location": "Golden Gate Park", "window_start": 1170, "window_end": 1320, "min_duration": 120},
    {"name": "Laura", "location": "Bayview", "window_start": 1275, "window_end": 1335, "min_duration": 15}
]

# Initialize Z3 solver
opt = Optimize()
opt.set("timeout", 300000)  # 5 minutes timeout

# Create variables
meet = []
s = []
e = []
loc_list = []

for i, friend in enumerate(friends_data):
    meet.append(Bool(f"meet_{friend['name']}"))
    s.append(Int(f"s_{friend['name']}"))
    e.append(Int(f"e_{friend['name']}"))
    loc_list.append(friend['location'])

# Constraints for each friend
for i in range(len(friends_data)):
    # If meeting the friend, enforce time window and duration
    opt.add(Implies(meet[i], s[i] >= friends_data[i]['window_start']))
    opt.add(Implies(meet[i], e[i] <= friends_data[i]['window_end']))
    opt.add(Implies(meet[i], e[i] - s[i] >= friends_data[i]['min_duration']))
    
    # Travel from Richmond District to the friend's location
    travel_time = travel_dict[("Richmond District", loc_list[i])]
    opt.add(Implies(meet[i], s[i] >= 540 + travel_time))

# Constraints for every pair of friends
for i in range(len(friends_data)):
    for j in range(i+1, len(friends_data)):
        time_ij = travel_dict[(loc_list[i], loc_list[j])]
        time_ji = travel_dict[(loc_list[j], loc_list[i])]
        # If both friends are met, ensure sufficient travel time between meetings
        opt.add(Implies(And(meet[i], meet[j]),
                        Or(s[j] >= e[i] + time_ij, 
                           s[i] >= e[j] + time_ji)))

# Objective: maximize the number of meetings
num_meetings = Sum([If(meet[i], 1, 0) for i in range(len(friends_data))])
opt.maximize(num_meetings)

# Solve the problem
itinerary_list = []
if opt.check() == sat:
    model = opt.model()
    # Collect scheduled meetings
    for i, friend in enumerate(friends_data):
        if is_true(model[meet[i]]):
            start_min = model[s[i]].as_long()
            end_min = model[e[i]].as_long()
            # Convert minutes to HH:MM format
            start_time = f"{start_min // 60:02d}:{start_min % 60:02d}"
            end_time = f"{end_min // 60:02d}:{end_min % 60:02d}"
            itinerary_list.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": start_time,
                "end_time": end_time
            })
    # Sort meetings by start time
    itinerary_list.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:5])))
else:
    itinerary_list = []  # No solution found

# Output the solution
print('SOLUTION:')
print(json.dumps({'itinerary': itinerary_list}))