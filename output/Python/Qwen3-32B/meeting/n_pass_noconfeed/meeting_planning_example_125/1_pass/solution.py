import json
from itertools import permutations

def to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Initial parameters
current_time = 9 * 60  # 9:00 AM in minutes
current_location = 'Embarcadero'

# Travel times between locations (in minutes)
travel_time = {
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Alamo Square'): 17,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Financial District'): 17,
}

# Friend constraints
friends = [
    {
        'name': 'Stephanie',
        'location': 'Financial District',
        'available_start': 8 * 60 + 15,  # 8:15 AM
        'available_end': 11 * 60 + 30,   # 11:30 AM
        'min_duration': 90
    },
    {
        'name': 'John',
        'location': 'Alamo Square',
        'available_start': 10 * 60 + 15,  # 10:15 AM
        'available_end': 20 * 60 + 45,    # 8:45 PM
        'min_duration': 30
    }
]

best_itinerary = []
best_num_meetings = 0

# Check all possible meeting order permutations
for perm in permutations(friends):
    itinerary = []
    valid = True
    time = current_time
    location = current_location
    
    for friend in perm:
        # Calculate travel time to friend's location
        from_loc = location
        to_loc = friend['location']
        if (from_loc, to_loc) not in travel_time:
            valid = False
            break
        travel_duration = travel_time[(from_loc, to_loc)]
        arrival_time = time + travel_duration
        
        # Determine earliest possible meeting start time
        start_time = max(arrival_time, friend['available_start'])
        
        # Check if meeting is possible with minimum duration
        end_time = start_time + friend['min_duration']
        if end_time > friend['available_end']:
            valid = False
            break
        
        # Record meeting details
        itinerary.append({
            'action': 'meet',
            'location': to_loc,
            'person': friend['name'],
            'start_time': start_time,
            'end_time': end_time
        })
        
        # Update current time and location
        time = end_time
        location = to_loc
    
    # Update best itinerary if current one is valid and better
    if valid and len(itinerary) > best_num_meetings:
        best_num_meetings = len(itinerary)
        best_itinerary = itinerary

# Format the best itinerary into required JSON structure
result = {
    "itinerary": [
        {
            "action": "meet",
            "location": meet["location"],
            "person": meet["person"],
            "start_time": to_time_str(meet["start_time"]),
            "end_time": to_time_str(meet["end_time"])
        }
        for meet in best_itinerary
    ]
}

print(json.dumps(result, indent=2))