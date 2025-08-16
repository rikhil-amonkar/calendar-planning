from z3 import *
import json

# Define travel times between locations
travel_time = {
    'The Castro': {
        'Marina District': 21,
        'Presidio': 20,
        'North Beach': 20,
        'Embarcadero': 22,
        'Haight-Ashbury': 6,
        'Golden Gate Park': 11,
        'Richmond District': 16,
        'Alamo Square': 8,
        'Financial District': 21,
        'Sunset District': 17
    },
    'Marina District': {
        'The Castro': 22,
        'Presidio': 10,
        'North Beach': 11,
        'Embarcadero': 14,
        'Haight-Ashbury': 16,
        'Golden Gate Park': 18,
        'Richmond District': 11,
        'Alamo Square': 15,
        'Financial District': 17,
        'Sunset District': 19
    },
    'Presidio': {
        'The Castro': 21,
        'Marina District': 11,
        'North Beach': 18,
        'Embarcadero': 20,
        'Haight-Ashbury': 15,
        'Golden Gate Park': 12,
        'Richmond District': 7,
        'Alamo Square': 19,
        'Financial District': 23,
        'Sunset District': 15
    },
    'North Beach': {
        'The Castro': 23,
        'Marina District': 9,
        'Presidio': 17,
        'Embarcadero': 6,
        'Haight-Ashbury': 18,
        'Golden Gate Park': 22,
        'Richmond District': 18,
        'Alamo Square': 16,
        'Financial District': 8,
        'Sunset District': 27
    },
    'Embarcadero': {
        'The Castro': 25,
        'Marina District': 12,
        'Presidio': 20,
        'North Beach': 5,
        'Haight-Ashbury': 21,
        'Golden Gate Park': 25,
        'Richmond District': 21,
        'Alamo Square': 19,
        'Financial District': 5,
        'Sunset District': 30
    },
    'Haight-Ashbury': {
        'The Castro': 6,
        'Marina District': 17,
        'Presidio': 15,
        'North Beach': 19,
        'Embarcadero': 20,
        'Golden Gate Park': 7,
        'Richmond District': 10,
        'Alamo Square': 5,
        'Financial District': 21,
        'Sunset District': 15
    },
    'Golden Gate Park': {
        'The Castro': 13,
        'Marina District': 16,
        'Presidio': 11,
        'North Beach': 23,
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Richmond District': 7,
        'Alamo Square': 9,
        'Financial District': 26,
        'Sunset District': 10
    },
    'Richmond District': {
        'The Castro': 16,
        'Marina District': 9,
        'Presidio': 7,
        'North Beach': 17,
        'Embarcadero': 19,
        'Haight-Ashbury': 10,
        'Golden Gate Park': 9,
        'Alamo Square': 13,
        'Financial District': 22,
        'Sunset District': 11
    },
    'Alamo Square': {
        'The Castro': 8,
        'Marina District': 15,
        'Presidio': 17,
        'North Beach': 15,
        'Embarcadero': 16,
        'Haight-Ashbury': 5,
        'Golden Gate Park': 9,
        'Richmond District': 11,
        'Financial District': 17,
        'Sunset District': 16
    },
    'Financial District': {
        'The Castro': 20,
        'Marina District': 15,
        'Presidio': 22,
        'North Beach': 7,
        'Embarcadero': 4,
        'Haight-Ashbury': 19,
        'Golden Gate Park': 23,
        'Richmond District': 21,
        'Alamo Square': 17,
        'Sunset District': 30
    },
    'Sunset District': {
        'The Castro': 17,
        'Marina District': 21,
        'Presidio': 16,
        'North Beach': 28,
        'Embarcadero': 30,
        'Haight-Ashbury': 15,
        'Golden Gate Park': 11,
        'Richmond District': 12,
        'Alamo Square': 17,
        'Financial District': 30
    }
}

# Define friends list with their details
friends = [
    {'name': 'Elizabeth', 'location': 'Marina District', 'available_start': 1140, 'available_end': 1245, 'required_duration': 105},
    {'name': 'Joshua', 'location': 'Presidio', 'available_start': 510, 'available_end': 795, 'required_duration': 105},
    {'name': 'Timothy', 'location': 'North Beach', 'available_start': 1185, 'available_end': 1320, 'required_duration': 90},
    {'name': 'David', 'location': 'Embarcadero', 'available_start': 645, 'available_end': 750, 'required_duration': 30},
    {'name': 'Kimberly', 'location': 'Haight-Ashbury', 'available_start': 1005, 'available_end': 1290, 'required_duration': 75},
    {'name': 'Lisa', 'location': 'Golden Gate Park', 'available_start': 1050, 'available_end': 1335, 'required_duration': 45},
    {'name': 'Ronald', 'location': 'Richmond District', 'available_start': 480, 'available_end': 570, 'required_duration': 90},
    {'name': 'Stephanie', 'location': 'Alamo Square', 'available_start': 930, 'available_end': 990, 'required_duration': 30},
    {'name': 'Helen', 'location': 'Financial District', 'available_start': 1050, 'available_end': 1110, 'required_duration': 45},
    {'name': 'Laura', 'location': 'Sunset District', 'available_start': 1065, 'available_end': 1275, 'required_duration': 90}
]

# Initialize Z3 solver
opt = Optimize()

# Create variables for each friend
includes = {}
starts = {}
ends = {}

for friend in friends:
    name = friend['name']
    includes[name] = Bool(f'include_{name}')
    starts[name] = Int(f'start_{name}')
    ends[name] = Int(f'end_{name}')
    opt.add(Implies(includes[name], ends[name] == starts[name] + friend['required_duration']))
    opt.add(Implies(includes[name], starts[name] >= friend['available_start']))
    opt.add(Implies(includes[name], ends[name] <= friend['available_end']))

# Add initial arrival time constraints
for friend in friends:
    name = friend['name']
    location = friend['location']
    init_time = 9 * 60  # 9:00 AM in minutes
    travel_castro_to_loc = travel_time['The Castro'][location]
    init_arrival = init_time + travel_castro_to_loc

    terms = [starts[name] >= init_arrival]
    for other in friends:
        if other['name'] == name:
            continue
        other_name = other['name']
        other_location = other['location']
        travel_time_other_to_loc = travel_time[other_location][location]
        terms.append(And(includes[other_name], starts[name] >= ends[other_name] + travel_time_other_to_loc))
    
    opt.add(Implies(includes[name], Or(*terms)))

# Add pairwise constraints between friends
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        friend1 = friends[i]
        friend2 = friends[j]
        name1 = friend1['name']
        name2 = friend2['name']
        loc1 = friend1['location']
        loc2 = friend2['location']
        travel1_to_2 = travel_time[loc1][loc2]
        travel2_to_1 = travel_time[loc2][loc1]
        opt.add(Implies(And(includes[name1], includes[name2]), 
                        Or(
                            starts[name1] >= ends[name2] + travel2_to_1,
                            starts[name2] >= ends[name1] + travel1_to_2
                        )))

# Maximize the number of included friends
opt.maximize(Sum([If(includes[name], 1, 0) for name in includes]))

# Check for solution
if opt.check() == sat:
    model = opt.model()
    result = []
    for friend in friends:
        name = friend['name']
        if is_true(model.evaluate(includes[name])):
            start_val = model.evaluate(starts[name]).as_long()
            end_val = start_val + friend['required_duration']
            start_h = start_val // 60
            start_m = start_val % 60
            end_h = end_val // 60
            end_m = end_val % 60
            start_time = f"{start_h:02d}:{start_m:02d}"
            end_time = f"{end_h:02d}:{end_m:02d}"
            result.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
    result.sort(key=lambda x: x["start_time"])
    print(json.dumps({"itinerary": result}))
else:
    print(json.dumps({"itinerary": []}))