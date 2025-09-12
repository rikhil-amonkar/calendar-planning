import json
from z3 import *

# Define friends with their parameters
friends = [
    {
        'name': 'Robert',
        'location': 'Chinatown',
        'availability_start': 7 * 60 + 45,  # 465
        'availability_end': 17 * 60 + 30,    # 1050
        'required_duration': 120
    },
    {
        'name': 'David',
        'location': 'Sunset District',
        'availability_start': 12 * 60 + 30,   # 750
        'availability_end': 19 * 60 + 45,     # 1185
        'required_duration': 45
    },
    {
        'name': 'Matthew',
        'location': 'Alamo Square',
        'availability_start': 8 * 60 + 45,    # 525
        'availability_end': 13 * 60 + 45,     # 825
        'required_duration': 90
    },
    {
        'name': 'Jessica',
        'location': 'Financial District',
        'availability_start': 9 * 60 + 30,    # 570
        'availability_end': 18 * 60 + 45,     # 1125
        'required_duration': 45
    },
    {
        'name': 'Melissa',
        'location': 'North Beach',
        'availability_start': 7 * 60 + 15,    # 435
        'availability_end': 16 * 60 + 45,     # 1005
        'required_duration': 45
    },
    {
        'name': 'Mark',
        'location': 'Embarcadero',
        'availability_start': 15 * 60 + 15,   # 915
        'availability_end': 17 * 60 + 0,      # 1020
        'required_duration': 45
    },
    {
        'name': 'Deborah',
        'location': 'Presidio',
        'availability_start': 19 * 60 + 0,    # 1140
        'availability_end': 19 * 60 + 45,     # 1185
        'required_duration': 45
    },
    {
        'name': 'Karen',
        'location': 'Golden Gate Park',
        'availability_start': 19 * 60 + 30,   # 1170
        'availability_end': 22 * 60 + 0,      # 1320
        'required_duration': 120
    },
    {
        'name': 'Laura',
        'location': 'Bayview',
        'availability_start': 21 * 60 + 15,   # 1275
        'availability_end': 22 * 60 + 15,     # 1335
        'required_duration': 15
    }
]

# Define travel times between locations
travel_times = {
    'Richmond District': {
        'Chinatown': 20,
        'Sunset District': 11,
        'Alamo Square': 13,
        'Financial District': 22,
        'North Beach': 17,
        'Embarcadero': 19,
        'Presidio': 7,
        'Golden Gate Park': 9,
        'Bayview': 27,
    },
    'Chinatown': {
        'Richmond District': 20,
        'Sunset District': 29,
        'Alamo Square': 17,
        'Financial District': 5,
        'North Beach': 3,
        'Embarcadero': 5,
        'Presidio': 19,
        'Golden Gate Park': 23,
        'Bayview': 20,
    },
    'Sunset District': {
        'Richmond District': 12,
        'Chinatown': 30,
        'Alamo Square': 17,
        'Financial District': 30,
        'North Beach': 28,
        'Embarcadero': 30,
        'Presidio': 16,
        'Golden Gate Park': 11,
        'Bayview': 22,
    },
    'Alamo Square': {
        'Richmond District': 11,
        'Chinatown': 15,
        'Sunset District': 16,
        'Financial District': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Presidio': 17,
        'Golden Gate Park': 9,
        'Bayview': 16,
    },
    'Financial District': {
        'Richmond District': 21,
        'Chinatown': 5,
        'Sunset District': 30,
        'Alamo Square': 17,
        'North Beach': 8,
        'Embarcadero': 4,
        'Presidio': 22,
        'Golden Gate Park': 23,
        'Bayview': 19,
    },
    'North Beach': {
        'Richmond District': 18,
        'Chinatown': 6,
        'Sunset District': 27,
        'Alamo Square': 16,
        'Financial District': 8,
        'Embarcadero': 6,
        'Presidio': 17,
        'Golden Gate Park': 22,
        'Bayview': 25,
    },
    'Embarcadero': {
        'Richmond District': 21,
        'Chinatown': 7,
        'Sunset District': 30,
        'Alamo Square': 19,
        'Financial District': 5,
        'North Beach': 5,
        'Presidio': 20,
        'Golden Gate Park': 25,
        'Bayview': 21,
    },
    'Presidio': {
        'Richmond District': 7,
        'Chinatown': 21,
        'Sunset District': 15,
        'Alamo Square': 19,
        'Financial District': 23,
        'North Beach': 18,
        'Embarcadero': 20,
        'Golden Gate Park': 12,
        'Bayview': 31,
    },
    'Golden Gate Park': {
        'Richmond District': 7,
        'Chinatown': 23,
        'Sunset District': 10,
        'Alamo Square': 9,
        'Financial District': 26,
        'North Beach': 23,
        'Embarcadero': 25,
        'Presidio': 11,
        'Bayview': 22,
    },
    'Bayview': {
        'Richmond District': 25,
        'Chinatown': 19,
        'Sunset District': 23,
        'Alamo Square': 16,
        'Financial District': 19,
        'North Beach': 22,
        'Embarcadero': 19,
        'Presidio': 32,
        'Golden Gate Park': 22,
    },
}

arrival_time = 9 * 60  # 540 minutes

# Create solver
solver = Optimize()

# Create variables
includes = []
starts = []
for friend in friends:
    include = Bool(f'include_{friend["name"]}')
    start = Int(f'start_{friend["name"]}')
    includes.append(include)
    starts.append(start)

# Add constraints for each friend
for i in range(len(friends)):
    friend = friends[i]
    include = includes[i]
    start = starts[i]
    duration = friend['required_duration']
    avail_start = friend['availability_start']
    avail_end = friend['availability_end']
    loc = friend['location']
    travel_from_richmond = travel_times['Richmond District'][loc]

    # If included, start must be within availability and after arrival + travel
    solver.add(Implies(include, start >= avail_start))
    solver.add(Implies(include, start + duration <= avail_end))
    solver.add(Implies(include, start >= arrival_time + travel_from_richmond))

# Add pairwise constraints between all friends
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        friend_i = friends[i]
        friend_j = friends[j]
        include_i = includes[i]
        include_j = includes[j]
        start_i = starts[i]
        start_j = starts[j]
        duration_i = friend_i['required_duration']
        duration_j = friend_j['required_duration']
        loc_i = friend_i['location']
        loc_j = friend_j['location']
        travel_ij = travel_times[loc_i][loc_j]
        travel_ji = travel_times[loc_j][loc_i]

        constraint = Implies(And(include_i, include_j), 
            Or(
                start_i >= start_j + duration_j + travel_ji,
                start_j >= start_i + duration_i + travel_ij
            )
        )
        solver.add(constraint)

# Objective: maximize the number of included friends
objective = Sum([If(include, 1, 0) for include in includes])
solver.maximize(objective)

# Check if the problem is satisfiable
result = solver.check()

if result == sat:
    model = solver.model()
    # Extract included friends and their start times
    included = []
    for i in range(len(friends)):
        if is_true(model.evaluate(includes[i])):
            start_time = model.evaluate(starts[i]).as_long()
            end_time = start_time + friends[i]['required_duration']
            included.append( (friends[i], start_time, end_time) )
    # Sort by start time to create the itinerary
    included.sort(key=lambda x: x[1])
    # Convert to JSON format
    itinerary = []
    for (friend, start, end) in included:
        start_str = f"{start//60}:{start%60:02d}"
        end_str = f"{end//60}:{end%60:02d}"
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": start_str,
            "end_time": end_str
        })
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")