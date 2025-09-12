import json
from z3 import *

# Define friends and their data
friends_data = [
    {
        'name': 'Amanda',
        'location': 'Marina District',
        'available_start': 885,
        'available_end': 1170,
        'min_duration': 105,
    },
    {
        'name': 'Melissa',
        'location': 'The Castro',
        'available_start': 570,
        'available_end': 1020,
        'min_duration': 30,
    },
    {
        'name': 'Jeffrey',
        'location': "Fisherman's Wharf",
        'available_start': 765,
        'available_end': 1125,
        'min_duration': 120,
    },
    {
        'name': 'Matthew',
        'location': 'Bayview',
        'available_start': 615,
        'available_end': 795,
        'min_duration': 30,
    },
    {
        'name': 'Nancy',
        'location': 'Pacific Heights',
        'available_start': 1020,
        'available_end': 1290,
        'min_duration': 105,
    },
    {
        'name': 'Karen',
        'location': 'Mission District',
        'available_start': 1050,
        'available_end': 1230,
        'min_duration': 105,
    },
    {
        'name': 'Robert',
        'location': 'Alamo Square',
        'available_start': 675,
        'available_end': 1050,
        'min_duration': 120,
    },
    {
        'name': 'Joseph',
        'location': 'Golden Gate Park',
        'available_start': 510,
        'available_end': 1275,
        'min_duration': 105,
    },
]

# Define travel times between locations
travel_times = {
    'Presidio': {
        'Marina District': 11,
        'The Castro': 21,
        "Fisherman's Wharf": 19,
        'Bayview': 31,
        'Pacific Heights': 11,
        'Mission District': 26,
        'Alamo Square': 19,
        'Golden Gate Park': 12,
    },
    'Marina District': {
        'Presidio': 10,
        'The Castro': 22,
        "Fisherman's Wharf": 10,
        'Bayview': 27,
        'Pacific Heights': 7,
        'Mission District': 20,
        'Alamo Square': 15,
        'Golden Gate Park': 18,
    },
    'The Castro': {
        'Presidio': 20,
        'Marina District': 21,
        "Fisherman's Wharf": 24,
        'Bayview': 19,
        'Pacific Heights': 16,
        'Mission District': 7,
        'Alamo Square': 8,
        'Golden Gate Park': 11,
    },
    "Fisherman's Wharf": {
        'Presidio': 17,
        'Marina District': 9,
        'The Castro': 27,
        'Bayview': 26,
        'Pacific Heights': 12,
        'Mission District': 22,
        'Alamo Square': 21,
        'Golden Gate Park': 25,
    },
    'Bayview': {
        'Presidio': 32,
        'Marina District': 27,
        'The Castro': 19,
        "Fisherman's Wharf": 25,
        'Pacific Heights': 23,
        'Mission District': 13,
        'Alamo Square': 16,
        'Golden Gate Park': 22,
    },
    'Pacific Heights': {
        'Presidio': 11,
        'Marina District': 6,
        'The Castro': 16,
        "Fisherman's Wharf": 13,
        'Bayview': 22,
        'Mission District': 15,
        'Alamo Square': 10,
        'Golden Gate Park': 15,
    },
    'Mission District': {
        'Presidio': 25,
        'Marina District': 19,
        'The Castro': 7,
        "Fisherman's Wharf": 22,
        'Bayview': 14,
        'Pacific Heights': 16,
        'Alamo Square': 11,
        'Golden Gate Park': 17,
    },
    'Alamo Square': {
        'Presidio': 17,
        'Marina District': 15,
        'The Castro': 8,
        "Fisherman's Wharf": 19,
        'Bayview': 16,
        'Pacific Heights': 10,
        'Mission District': 10,
        'Golden Gate Park': 9,
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Marina District': 16,
        'The Castro': 13,
        "Fisherman's Wharf": 24,
        'Bayview': 23,
        'Pacific Heights': 16,
        'Mission District': 17,
        'Alamo Square': 9,
    },
}

# Create Z3 solver
solver = Optimize()

# Create variables for each friend
friends = []
for f in friends_data:
    name = f['name']
    include = Bool(f"include_{name}")
    start = Int(f"start_{name}")
    end = Int(f"end_{name}")
    friends.append({
        'name': name,
        'location': f['location'],
        'available_start': f['available_start'],
        'available_end': f['available_end'],
        'min_duration': f['min_duration'],
        'include': include,
        'start': start,
        'end': end,
    })

# Add constraints for each friend
for f in friends:
    include = f['include']
    start = f['start']
    end = f['end']
    available_start = f['available_start']
    available_end = f['available_end']
    min_duration = f['min_duration']
    location = f['location']
    travel_time_from_presidio = travel_times['Presidio'][location]
    
    # If included, add constraints
    solver.add(Implies(include, start >= available_start))
    solver.add(Implies(include, end >= start + min_duration))
    solver.add(Implies(include, end <= available_end))
    solver.add(Implies(include, start >= 540 + travel_time_from_presidio))

# Add pairwise constraints between friends
for i in range(len(friends)):
    for j in range(i + 1, len(friends)):
        A = friends[i]
        B = friends[j]
        include_A = A['include']
        include_B = B['include']
        start_A = A['start']
        end_A = A['end']
        location_A = A['location']
        start_B = B['start']
        end_B = B['end']
        location_B = B['location']
        
        # Get travel times between their locations
        travel_time_A_to_B = travel_times[location_A][location_B]
        travel_time_B_to_A = travel_times[location_B][location_A]
        
        # Add constraint: if both are included, then either A comes before B or B comes before A
        constraint = Implies(And(include_A, include_B), Or(
            start_A >= end_B + travel_time_B_to_A,
            start_B >= end_A + travel_time_A_to_B
        ))
        solver.add(constraint)

# Maximize the number of included friends
sum_include = Sum([If(f['include'], 1, 0) for f in friends])
solver.maximize(sum_include)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    # Extract included friends
    included_friends = []
    for f in friends:
        if is_true(model.eval(f['include'])):
            start_val = model.eval(f['start']).as_long()
            end_val = model.eval(f['end']).as_long()
            included_friends.append({
                'name': f['name'],
                'location': f['location'],
                'start': start_val,
                'end': end_val,
            })
    
    # Sort by start time
    included_friends.sort(key=lambda x: x['start'])
    
    # Convert to H:MM format
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Generate itinerary
    itinerary = []
    for friend in included_friends:
        itinerary.append({
            "action": "meet",
            "location": friend['location'],
            "person": friend['name'],
            "start_time": format_time(friend['start']),
            "end_time": format_time(friend['end']),
        })
    
    # Output JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print(json.dumps({"itinerary": []}))