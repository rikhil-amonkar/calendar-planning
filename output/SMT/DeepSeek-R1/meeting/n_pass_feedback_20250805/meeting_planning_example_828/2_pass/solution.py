from z3 import *

# Define travel times between locations
travel_times = {
    'Marina District': {
        'Marina District': 0,
        'Richmond District': 11,
        'Union Square': 16,
        'Nob Hill': 12,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 18,
        'Embarcadero': 14,
        'Financial District': 17,
        'North Beach': 11,
        'Presidio': 10
    },
    'Richmond District': {
        'Marina District': 9,
        'Richmond District': 0,
        'Union Square': 21,
        'Nob Hill': 17,
        'Fisherman\'s Wharf': 18,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Financial District': 22,
        'North Beach': 17,
        'Presidio': 7
    },
    'Union Square': {
        'Marina District': 18,
        'Richmond District': 20,
        'Union Square': 0,
        'Nob Hill': 9,
        'Fisherman\'s Wharf': 15,
        'Golden Gate Park': 22,
        'Embarcadero': 11,
        'Financial District': 9,
        'North Beach': 10,
        'Presidio': 24
    },
    'Nob Hill': {
        'Marina District': 11,
        'Richmond District': 14,
        'Union Square': 7,
        'Nob Hill': 0,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 17,
        'Embarcadero': 9,
        'Financial District': 9,
        'North Beach': 8,
        'Presidio': 17
    },
    'Fisherman\'s Wharf': {
        'Marina District': 9,
        'Richmond District': 18,
        'Union Square': 13,
        'Nob Hill': 11,
        'Fisherman\'s Wharf': 0,
        'Golden Gate Park': 25,
        'Embarcadero': 8,
        'Financial District': 11,
        'North Beach': 6,
        'Presidio': 17
    },
    'Golden Gate Park': {
        'Marina District': 16,
        'Richmond District': 7,
        'Union Square': 22,
        'Nob Hill': 20,
        'Fisherman\'s Wharf': 24,
        'Golden Gate Park': 0,
        'Embarcadero': 25,
        'Financial District': 26,
        'North Beach': 23,
        'Presidio': 11
    },
    'Embarcadero': {
        'Marina District': 12,
        'Richmond District': 21,
        'Union Square': 10,
        'Nob Hill': 10,
        'Fisherman\'s Wharf': 6,
        'Golden Gate Park': 25,
        'Embarcadero': 0,
        'Financial District': 5,
        'North Beach': 5,
        'Presidio': 20
    },
    'Financial District': {
        'Marina District': 15,
        'Richmond District': 21,
        'Union Square': 9,
        'Nob Hill': 8,
        'Fisherman\'s Wharf': 10,
        'Golden Gate Park': 23,
        'Embarcadero': 4,
        'Financial District': 0,
        'North Beach': 7,
        'Presidio': 22
    },
    'North Beach': {
        'Marina District': 9,
        'Richmond District': 18,
        'Union Square': 7,
        'Nob Hill': 7,
        'Fisherman\'s Wharf': 5,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Financial District': 8,
        'North Beach': 0,
        'Presidio': 17
    },
    'Presidio': {
        'Marina District': 11,
        'Richmond District': 7,
        'Union Square': 22,
        'Nob Hill': 18,
        'Fisherman\'s Wharf': 19,
        'Golden Gate Park': 12,
        'Embarcadero': 20,
        'Financial District': 23,
        'North Beach': 18,
        'Presidio': 0
    }
}

# Define friends and their availability (in minutes from 9:00 AM)
friends = [
    {'name': 'Stephanie', 'location': 'Richmond District', 'start': 435, 'end': 750, 'min_dur': 75},
    {'name': 'William', 'location': 'Union Square', 'start': 105, 'end': 510, 'min_dur': 45},
    {'name': 'Elizabeth', 'location': 'Nob Hill', 'start': 195, 'end': 360, 'min_dur': 105},
    {'name': 'Joseph', 'location': 'Fisherman\'s Wharf', 'start': 225, 'end': 300, 'min_dur': 75},
    {'name': 'Anthony', 'location': 'Golden Gate Park', 'start': 240, 'end': 690, 'min_dur': 75},
    {'name': 'Barbara', 'location': 'Embarcadero', 'start': 615, 'end': 690, 'min_dur': 75},
    {'name': 'Carol', 'location': 'Financial District', 'start': 165, 'end': 435, 'min_dur': 60},
    {'name': 'Sandra', 'location': 'North Beach', 'start': 60, 'end': 210, 'min_dur': 15},
    {'name': 'Kenneth', 'location': 'Presidio', 'start': 735, 'end': 795, 'min_dur': 45}
]

# Starting location and time
start_location = 'Marina District'
start_time = 0  # 9:00 AM

# Initialize Z3 optimizer
opt = Optimize()

# Create variables for meetings
meet_vars = {}
start_vars = {}
end_vars = {}
location_vars = {}

for friend in friends:
    name = friend['name']
    meet_vars[name] = Bool(name)
    start_vars[name] = Int(f"start_{name}")
    end_vars[name] = Int(f"end_{name}")
    location_vars[name] = friend['location']

# Constraints for each meeting
for friend in friends:
    name = friend['name']
    # If meeting is scheduled, it must be within availability window and meet minimum duration
    opt.add(Implies(meet_vars[name], start_vars[name] >= friend['start']))
    opt.add(Implies(meet_vars[name], end_vars[name] <= friend['end']))
    opt.add(Implies(meet_vars[name], end_vars[name] - start_vars[name] >= friend['min_dur']))

# Constraints for travel from starting location to first meeting
for friend in friends:
    name = friend['name']
    travel_time = travel_times[start_location][friend['location']]
    opt.add(Implies(meet_vars[name], start_vars[name] >= start_time + travel_time))

# Constraints for travel between meetings
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        name1 = friends[i]['name']
        name2 = friends[j]['name']
        loc1 = friends[i]['location']
        loc2 = friends[j]['location']
        travel_time_1_to_2 = travel_times[loc1][loc2]
        travel_time_2_to_1 = travel_times[loc2][loc1]
        
        # If both meetings are scheduled, ensure sufficient travel time between them
        both_meet = And(meet_vars[name1], meet_vars[name2])
        opt.add(Implies(both_meet, Or(
            end_vars[name1] + travel_time_1_to_2 <= start_vars[name2],
            end_vars[name2] + travel_time_2_to_1 <= start_vars[name1]
        )))

# Maximize the number of meetings scheduled
opt.maximize(Sum([If(meet_vars[friend['name']], 1, 0) for friend in friends]))

# Solve the model
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    for friend in friends:
        name = friend['name']
        if model.evaluate(meet_vars[name]):
            start_min = model.evaluate(start_vars[name]).as_long()
            end_min = model.evaluate(end_vars[name]).as_long()
            # Convert minutes to time string (24-hour format)
            start_hour = 9 + start_min // 60
            start_minute = start_min % 60
            end_hour = 9 + end_min // 60
            end_minute = end_min % 60
            start_time_str = f"{start_hour:02d}:{start_minute:02d}"
            end_time_str = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_time_str,
                "end_time": end_time_str
            })
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x['start_time'])
    print("SOLUTION:")
    print(f'{{"itinerary": {itinerary}}}')
else:
    print("SOLUTION:")
    print('{"itinerary": []}')