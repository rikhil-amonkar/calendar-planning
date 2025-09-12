import json
from z3 import *

# Define friends and their constraints
locations_dict = {
    'Presidio': 0,
    'Haight-Ashbury': 1,
    'Nob Hill': 2,
    'Russian Hill': 3,
    'North Beach': 4,
    'Chinatown': 5,
    'Union Square': 6,
    'Embarcadero': 7,
    'Financial District': 8,
    'Marina District': 9
}

friends = [
    {
        'name': 'Karen',
        'location': 'Haight-Ashbury',
        'available_start': 9 * 60,  # 9:00 AM
        'available_end': 21 * 60,   # 9:00 PM
        'required_duration': 45,
        'location_code': locations_dict['Haight-Ashbury']
    },
    {
        'name': 'Jessica',
        'location': 'Nob Hill',
        'available_start': 13 * 60 + 45,  # 1:45 PM
        'available_end': 21 * 60,         # 9:00 PM
        'required_duration': 90,
        'location_code': locations_dict['Nob Hill']
    },
    {
        'name': 'Brian',
        'location': 'Russian Hill',
        'available_start': 15 * 60 + 30,  # 3:30 PM
        'available_end': 21 * 60 + 45,    # 9:45 PM
        'required_duration': 60,
        'location_code': locations_dict['Russian Hill']
    },
    {
        'name': 'Kenneth',
        'location': 'North Beach',
        'available_start': 9 * 60 + 45,   # 9:45 AM
        'available_end': 21 * 60,         # 9:00 PM
        'required_duration': 30,
        'location_code': locations_dict['North Beach']
    },
    {
        'name': 'Jason',
        'location': 'Chinatown',
        'available_start': 8 * 60 + 15,   # 8:15 AM
        'available_end': 11 * 60 + 45,    # 11:45 AM
        'required_duration': 75,
        'location_code': locations_dict['Chinatown']
    },
    {
        'name': 'Stephanie',
        'location': 'Union Square',
        'available_start': 14 * 60 + 45,  # 2:45 PM
        'available_end': 18 * 60 + 45,    # 6:45 PM
        'required_duration': 105,
        'location_code': locations_dict['Union Square']
    },
    {
        'name': 'Kimberly',
        'location': 'Embarcadero',
        'available_start': 9 * 60 + 45,   # 9:45 AM
        'available_end': 19 * 60 + 30,    # 7:30 PM
        'required_duration': 75,
        'location_code': locations_dict['Embarcadero']
    },
    {
        'name': 'Steven',
        'location': 'Financial District',
        'available_start': 7 * 60 + 15,   # 7:15 AM
        'available_end': 21 * 60 + 15,    # 9:15 PM
        'required_duration': 60,
        'location_code': locations_dict['Financial District']
    },
    {
        'name': 'Mark',
        'location': 'Marina District',
        'available_start': 10 * 60 + 15,  # 10:15 AM
        'available_end': 13 * 60,         # 1:00 PM
        'required_duration': 75,
        'location_code': locations_dict['Marina District']
    }
]

# Travel time matrix
travel_time = [
    [0, 15, 18, 14, 18, 21, 22, 20, 23, 11],
    [15, 0, 15, 17, 19, 19, 19, 20, 21, 17],
    [17, 13, 0, 5, 8, 6, 7, 9, 9, 11],
    [14, 17, 5, 0, 5, 9, 10, 8, 11, 7],
    [17, 18, 7, 4, 0, 6, 7, 6, 8, 9],
    [19, 19, 9, 7, 6, 0, 7, 5, 5, 12],
    [24, 18, 9, 13, 10, 7, 0, 11, 9, 18],
    [20, 21, 10, 8, 5, 7, 10, 0, 5, 12],
    [22, 19, 8, 11, 7, 5, 9, 4, 0, 15],
    [10, 16, 12, 8, 11, 15, 16, 14, 17, 0]
]

# Z3 setup
solver = Optimize()

num_positions = 9

# Create variables
friend_vars = [Int(f'friend_{i}') for i in range(num_positions)]
start_vars = [Int(f'start_{i}') for i in range(num_positions)]
end_vars = [Int(f'end_{i}') for i in range(num_positions)]

# Constraints for friend_vars to be between 0-9
for i in range(num_positions):
    solver.add(And(friend_vars[i] >= 0, friend_vars[i] <= 9))

# Constraints for each friend's meeting times
for i in range(num_positions):
    f = friend_vars[i]
    s = start_vars[i]
    e = end_vars[i]
    constraints = []
    for idx in range(9):
        avail_start = friends[idx]['available_start']
        avail_end = friends[idx]['available_end']
        duration = friends[idx]['required_duration']
        constraints.append(
            If(f == idx,
               And(s >= avail_start, e <= avail_end, e == s + duration),
               True)
        )
    solver.add(And(*constraints))

# First position: start time after travel from Presidio
i = 0
s = start_vars[i]
f = friend_vars[i]
constraints = []
for idx in range(9):
    loc_code = friends[idx]['location_code']
    travel = travel_time[0][loc_code]
    constraints.append(
        If(f == idx,
           s >= 540 + travel,
           True)
    )
solver.add(And(*constraints))

# Subsequent positions: start time after previous end + travel
for i in range(1, num_positions):
    s = start_vars[i]
    prev_e = end_vars[i-1]
    constraints = []
    for prev_idx in range(9):
        for curr_idx in range(9):
            prev_loc = friends[prev_idx]['location_code']
            curr_loc = friends[curr_idx]['location_code']
            travel = travel_time[prev_loc][curr_loc]
            constraints.append(
                If(And(friend_vars[i-1] == prev_idx, friend_vars[i] == curr_idx),
                   s >= prev_e + travel,
                   True)
            )
    solver.add(And(*constraints))

# Ensure each friend is scheduled at most once
for i in range(num_positions):
    for j in range(i+1, num_positions):
        solver.add(Implies(And(friend_vars[i] != 9, friend_vars[j] != 9), friend_vars[i] != friend_vars[j]))

# Objective: maximize the number of friends met
count = Sum([If(friend_vars[i] != 9, 1, 0) for i in range(num_positions)])
solver.maximize(count)

# Solve
if solver.check() == sat:
    model = solver.model()
    # Extract the meetings
    itinerary = []
    for i in range(num_positions):
        f_idx = model.evaluate(friend_vars[i])
        if f_idx != 9:
            f_idx_val = int(str(f_idx))
            start = int(str(model.evaluate(start_vars[i])))
            end = int(str(model.evaluate(end_vars[i])))
            friend = friends[f_idx_val]
            # Convert start and end to H:MM format
            def to_time(minutes):
                hours = minutes // 60
                mins = minutes % 60
                return f"{hours}:{mins:02d}"
            itinerary.append({
                "action": "meet",
                "location": friend['location'],
                "person": friend['name'],
                "start_time": to_time(start),
                "end_time": to_time(end)
            })
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print(json.dumps({"itinerary": []}))