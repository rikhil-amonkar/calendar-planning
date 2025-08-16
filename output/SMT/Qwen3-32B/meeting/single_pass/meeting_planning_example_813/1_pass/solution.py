from z3 import *
import json

# Define friends and their data
friends = [
    {'name': 'Joshua', 'location': 'Embarcadero', 'available_start': 9*60 + 45, 'available_end': 18*60, 'required_duration': 105},
    {'name': 'Jeffrey', 'location': 'Bayview', 'available_start': 9*60 + 45, 'available_end': 20*60 + 15, 'required_duration': 75},
    {'name': 'Charles', 'location': 'Union Square', 'available_start': 10*60 + 45, 'available_end': 20*60 + 15, 'required_duration': 120},
    {'name': 'Joseph', 'location': 'Chinatown', 'available_start': 7*60, 'available_end': 15*60 + 30, 'required_duration': 60},
    {'name': 'Elizabeth', 'location': 'Sunset District', 'available_start': 9*60, 'available_end': 9*60 + 45, 'required_duration': 45},
    {'name': 'Matthew', 'location': 'Golden Gate Park', 'available_start': 11*60, 'available_end': 19*60 + 30, 'required_duration': 45},
    {'name': 'Carol', 'location': 'Financial District', 'available_start': 10*60 + 45, 'available_end': 11*60 + 15, 'required_duration': 15},
    {'name': 'Paul', 'location': 'Haight-Ashbury', 'available_start': 19*60 + 15, 'available_end': 20*60 + 30, 'required_duration': 15},
    {'name': 'Rebecca', 'location': 'Mission District', 'available_start': 17*60, 'available_end': 21*60 + 45, 'required_duration': 45},
]

# Define travel times between locations
locations = ['Marina District', 'Embarcadero', 'Bayview', 'Union Square', 'Chinatown', 'Sunset District', 'Golden Gate Park', 'Financial District', 'Haight-Ashbury', 'Mission District']
travel_time = {
    'Marina District': {
        'Embarcadero': 14,
        'Bayview': 27,
        'Union Square': 16,
        'Chinatown': 15,
        'Sunset District': 19,
        'Golden Gate Park': 18,
        'Financial District': 17,
        'Haight-Ashbury': 16,
        'Mission District': 20,
    },
    'Embarcadero': {
        'Marina District': 12,
        'Bayview': 21,
        'Union Square': 10,
        'Chinatown': 7,
        'Sunset District': 30,
        'Golden Gate Park': 25,
        'Financial District': 5,
        'Haight-Ashbury': 21,
        'Mission District': 20,
    },
    'Bayview': {
        'Marina District': 27,
        'Embarcadero': 19,
        'Union Square': 18,
        'Chinatown': 19,
        'Sunset District': 23,
        'Golden Gate Park': 22,
        'Financial District': 19,
        'Haight-Ashbury': 19,
        'Mission District': 13,
    },
    'Union Square': {
        'Marina District': 18,
        'Embarcadero': 11,
        'Bayview': 15,
        'Chinatown': 7,
        'Sunset District': 27,
        'Golden Gate Park': 22,
        'Financial District': 9,
        'Haight-Ashbury': 18,
        'Mission District': 14,
    },
    'Chinatown': {
        'Marina District': 12,
        'Embarcadero': 5,
        'Bayview': 20,
        'Union Square': 7,
        'Sunset District': 29,
        'Golden Gate Park': 23,
        'Financial District': 5,
        'Haight-Ashbury': 19,
        'Mission District': 17,
    },
    'Sunset District': {
        'Marina District': 21,
        'Embarcadero': 30,
        'Bayview': 22,
        'Union Square': 30,
        'Chinatown': 30,
        'Golden Gate Park': 11,
        'Financial District': 30,
        'Haight-Ashbury': 15,
        'Mission District': 25,
    },
    'Golden Gate Park': {
        'Marina District': 16,
        'Embarcadero': 25,
        'Bayview': 23,
        'Union Square': 22,
        'Chinatown': 23,
        'Sunset District': 10,
        'Financial District': 26,
        'Haight-Ashbury': 7,
        'Mission District': 17,
    },
    'Financial District': {
        'Marina District': 15,
        'Embarcadero': 4,
        'Bayview': 19,
        'Union Square': 9,
        'Chinatown': 5,
        'Sunset District': 30,
        'Golden Gate Park': 23,
        'Haight-Ashbury': 19,
        'Mission District': 17,
    },
    'Haight-Ashbury': {
        'Marina District': 17,
        'Embarcadero': 20,
        'Bayview': 18,
        'Union Square': 19,
        'Chinatown': 19,
        'Sunset District': 15,
        'Golden Gate Park': 7,
        'Financial District': 21,
        'Mission District': 11,
    },
    'Mission District': {
        'Marina District': 19,
        'Embarcadero': 19,
        'Bayview': 14,
        'Union Square': 15,
        'Chinatown': 16,
        'Sunset District': 24,
        'Golden Gate Park': 17,
        'Financial District': 15,
        'Haight-Ashbury': 12,
    },
}

# Create Z3 solver
s = Solver()

max_steps = 9
num_friends = len(friends)

# Variables for each step
selected_friend = [Int(f"selected_friend_{i}") for i in range(max_steps)]
start_time = [Int(f"start_time_{i}") for i in range(max_steps)]
end_time = [Int(f"end_time_{i}") for i in range(max_steps)]

# Constraints for each step
for i in range(max_steps):
    # selected_friend[i] is between -1 and num_friends-1
    s.add(selected_friend[i] >= -1)
    s.add(selected_friend[i] <= num_friends - 1)

    # If selected_friend[i] is not -1, then:
    # start_time[i] >= available_start of the friend
    # end_time[i] = start_time[i] + required_duration
    # end_time[i] <= available_end of the friend
    for k in range(num_friends):
        friend = friends[k]
        available_start = friend['available_start']
        available_end = friend['available_end']
        duration = friend['required_duration']
        s.add(Implies(selected_friend[i] == k, start_time[i] >= available_start))
        s.add(Implies(selected_friend[i] == k, end_time[i] == start_time[i] + duration))
        s.add(Implies(selected_friend[i] == k, end_time[i] <= available_end))

    # For the first step (i=0), start_time must be >= 9:00 AM + travel time from Marina to friend's location
    if i == 0:
        for k in range(num_friends):
            friend_loc = friends[k]['location']
            travel = travel_time['Marina District'][friend_loc]
            min_start = 9 * 60 + travel
            s.add(Implies(selected_friend[i] == k, start_time[i] >= min_start))

# Constraints for contiguous steps
for i in range(1, max_steps):
    for j in range(i):
        s.add(Implies(selected_friend[i] >= 0, selected_friend[j] >= 0))

# Constraints for travel time between consecutive steps
for i in range(1, max_steps):
    for p in range(num_friends):  # previous friend index
        for k in range(num_friends):  # current friend index
            if p == k:
                continue  # can't select same friend twice
            prev_loc = friends[p]['location']
            curr_loc = friends[k]['location']
            travel = travel_time[prev_loc][curr_loc]
            s.add(Implies(And(selected_friend[i-1] == p, selected_friend[i] == k), start_time[i] >= end_time[i-1] + travel))

# Constraints to ensure no duplicate friends
for i in range(max_steps):
    for j in range(i+1, max_steps):
        for k in range(num_friends):
            s.add(Implies(And(selected_friend[i] == k, selected_friend[j] == k), False))

# Maximize the number of friends selected
count = Sum([If(selected_friend[i] >= 0, 1, 0) for i in range(max_steps)])
s.maximize(count)

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    # Extract the selected friends and their times
    itinerary = []
    for i in range(max_steps):
        sf = model[selected_friend[i]].as_long()
        if sf >= 0:
            friend = friends[sf]
            st = model[start_time[i]].as_long()
            et = model[end_time[i]].as_long()
            # Convert to HH:MM
            def to_time_str(minutes):
                h = minutes // 60
                m = minutes % 60
                return f"{h:02d}:{m:02d}"
            start_time_str = to_time_str(st)
            end_time_str = to_time_str(et)
            itinerary.append({
                "action": "meet",
                "person": friend['name'],
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    # Output the JSON
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")