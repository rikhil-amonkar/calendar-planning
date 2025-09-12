from z3 import *
import json

# Define friends with their details (index 0 is unused, friends 1-10)
friends = [None,
    {
        'name': 'Nancy',
        'location': 'Nob Hill',
        'available_start': 8 * 60 + 15,  # 8:15 AM
        'available_end': 12 * 60 + 45,   # 12:45 PM
        'duration': 90,
    },
    {
        'name': 'David',
        'location': 'Marina District',
        'available_start': 11 * 60 + 15,  # 11:15 AM
        'available_end': 13 * 60 + 15,   # 1:15 PM
        'duration': 120,
    },
    {
        'name': 'Stephanie',
        'location': 'Haight-Ashbury',
        'available_start': 10 * 60 + 15,  # 10:15 AM
        'available_end': 12 * 60 + 15,   # 12:15 PM
        'duration': 75,
    },
    {
        'name': 'Elizabeth',
        'location': 'Union Square',
        'available_start': 11 * 60 + 30,  # 11:30 AM
        'available_end': 21 * 60 + 0,    # 9:00 PM
        'duration': 60,
    },
    {
        'name': 'Robert',
        'location': 'Financial District',
        'available_start': 13 * 60 + 15,  # 1:15 PM
        'available_end': 15 * 60 + 15,   # 3:15 PM
        'duration': 45,
    },
    {
        'name': 'Brian',
        'location': 'Embarcadero',
        'available_start': 14 * 60 + 15,  # 2:15 PM
        'available_end': 16 * 60 + 0,    # 4:00 PM
        'duration': 105,
    },
    {
        'name': 'Melissa',
        'location': 'Richmond District',
        'available_start': 14 * 60 + 0,   # 2:00 PM
        'available_end': 19 * 60 + 30,    # 7:30 PM
        'duration': 30,
    },
    {
        'name': 'James',
        'location': 'Presidio',
        'available_start': 15 * 60 + 0,   # 3:00 PM
        'available_end': 18 * 60 + 15,    # 6:15 PM
        'duration': 120,
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'available_start': 17 * 60 + 30,  # 5:30 PM
        'available_end': 20 * 60 + 30,    # 8:30 PM
        'duration': 15,
    },
    {
        'name': 'Sarah',
        'location': 'Golden Gate Park',
        'available_start': 17 * 60 + 0,   # 5:00 PM
        'available_end': 19 * 60 + 15,    # 7:15 PM
        'duration': 75,
    },
]

# Define travel times between locations
locations = [
    'The Castro',
    'North Beach',
    'Golden Gate Park',
    'Embarcadero',
    'Haight-Ashbury',
    'Richmond District',
    'Nob Hill',
    'Marina District',
    'Presidio',
    'Union Square',
    'Financial District',
]

travel_times = {
    'The Castro': {
        'North Beach': 20,
        'Golden Gate Park': 11,
        'Embarcadero': 22,
        'Haight-Ashbury': 6,
        'Richmond District': 16,
        'Nob Hill': 16,
        'Marina District': 21,
        'Presidio': 20,
        'Union Square': 19,
        'Financial District': 21,
    },
    'North Beach': {
        'The Castro': 23,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Haight-Ashbury': 18,
        'Richmond District': 18,
        'Nob Hill': 7,
        'Marina District': 9,
        'Presidio': 17,
        'Union Square': 7,
        'Financial District': 8,
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'North Beach': 23,
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Richmond District': 7,
        'Nob Hill': 20,
        'Marina District': 16,
        'Presidio': 11,
        'Union Square': 22,
        'Financial District': 26,
    },
    'Embarcadero': {
        'The Castro': 25,
        'North Beach': 5,
        'Golden Gate Park': 25,
        'Haight-Ashbury': 21,
        'Richmond District': 21,
        'Nob Hill': 10,
        'Marina District': 12,
        'Presidio': 20,
        'Union Square': 10,
        'Financial District': 5,
    },
    'Haight-Ashbury': {
        'The Castro': 6,
        'North Beach': 19,
        'Golden Gate Park': 7,
        'Embarcadero': 20,
        'Richmond District': 10,
        'Nob Hill': 15,
        'Marina District': 17,
        'Presidio': 15,
        'Union Square': 19,
        'Financial District': 21,
    },
    'Richmond District': {
        'The Castro': 16,
        'North Beach': 17,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Haight-Ashbury': 10,
        'Nob Hill': 17,
        'Marina District': 9,
        'Presidio': 7,
        'Union Square': 21,
        'Financial District': 22,
    },
    'Nob Hill': {
        'The Castro': 17,
        'North Beach': 8,
        'Golden Gate Park': 17,
        'Embarcadero': 9,
        'Haight-Ashbury': 13,
        'Richmond District': 14,
        'Marina District': 11,
        'Presidio': 17,
        'Union Square': 7,
        'Financial District': 9,
    },
    'Marina District': {
        'The Castro': 22,
        'North Beach': 11,
        'Golden Gate Park': 18,
        'Embarcadero': 14,
        'Haight-Ashbury': 16,
        'Richmond District': 11,
        'Nob Hill': 12,
        'Presidio': 10,
        'Union Square': 16,
        'Financial District': 17,
    },
    'Presidio': {
        'The Castro': 21,
        'North Beach': 18,
        'Golden Gate Park': 12,
        'Embarcadero': 20,
        'Haight-Ashbury': 15,
        'Richmond District': 7,
        'Nob Hill': 18,
        'Marina District': 11,
        'Union Square': 22,
        'Financial District': 23,
    },
    'Union Square': {
        'The Castro': 17,
        'North Beach': 10,
        'Golden Gate Park': 22,
        'Embarcadero': 11,
        'Haight-Ashbury': 18,
        'Richmond District': 20,
        'Nob Hill': 9,
        'Marina District': 18,
        'Presidio': 24,
        'Financial District': 9,
    },
    'Financial District': {
        'The Castro': 20,
        'North Beach': 7,
        'Golden Gate Park': 23,
        'Embarcadero': 4,
        'Haight-Ashbury': 19,
        'Richmond District': 21,
        'Nob Hill': 8,
        'Marina District': 15,
        'Presidio': 22,
        'Union Square': 9,
    },
}

# Z3 solver setup
s = Optimize()

# Variables for each of the 10 positions in the itinerary
friend_vars = [Int(f'friend_{i}') for i in range(10)]
start_vars = [Int(f'start_{i}') for i in range(10)]
end_vars = [Int(f'end_{i}') for i in range(10)]

# Constrain friend indices to be 0 (no meeting) or 1-10 (friends)
for i in range(10):
    s.add(And(friend_vars[i] >= 0, friend_vars[i] <= 10))

# Add constraints for each possible meeting in each position
for i in range(10):
    for j in range(11):  # j ranges from 0 to 10
        if j == 0:
            continue  # skip no-meeting
        f = friends[j]
        s.add(Implies(friend_vars[i] == j, start_vars[i] >= f['available_start']))
        s.add(Implies(friend_vars[i] == j, end_vars[i] == start_vars[i] + f['duration']))
        s.add(Implies(friend_vars[i] == j, end_vars[i] <= f['available_end']))
        
        if i == 0:
            # First position: start time must be after arrival at The Castro (9:00 AM = 540 min) plus travel time
            travel_time = travel_times['The Castro'][f['location']]
            s.add(Implies(friend_vars[i] == j, start_vars[i] >= 540 + travel_time))
        else:
            # For subsequent positions, ensure travel time from previous location
            for k in range(11):
                if k == 0:
                    continue  # skip no-meeting for previous
                prev_f = friends[k]
                travel_time = travel_times[prev_f['location']][f['location']]
                s.add(Implies(And(friend_vars[i] == j, friend_vars[i-1] == k), 
                              start_vars[i] >= end_vars[i-1] + travel_time))

# Maximize the number of meetings
total_meetings = Sum([If(friend_vars[i] != 0, 1, 0) for i in range(10)])
s.maximize(total_meetings)

# Solve and extract results
if s.check() == sat:
    model = s.model()
    itinerary = []
    for i in range(10):
        friend_idx = model.evaluate(friend_vars[i]).as_long()
        if friend_idx != 0:
            f = friends[friend_idx]
            start = model.evaluate(start_vars[i]).as_long()
            end = model.evaluate(end_vars[i]).as_long()
            def to_time_str(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours}:{mins:02d}"
            start_str = to_time_str(start)
            end_str = to_time_str(end)
            itinerary.append({
                "action": "meet",
                "location": f['location'],
                "person": f['name'],
                "start_time": start_str,
                "end_time": end_str
            })
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No solution found.")