import json
from itertools import permutations

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Define friends' constraints
friends = [
    {
        'name': 'Carol',
        'location': 'Marina District',
        'available_start': 11*60 + 30,  # 11:30 AM
        'available_end': 15*60,        # 3:00 PM
        'required_duration': 60        # 60 minutes
    },
    {
        'name': 'Jessica',
        'location': 'Pacific Heights',
        'available_start': 15*60 + 30,  # 3:30 PM
        'available_end': 16*60 + 45,    # 4:45 PM
        'required_duration': 45        # 45 minutes
    }
]

# Define travel times between locations
travel_time = {
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Marina District'): 9,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Marina District'): 6,
    ('Marina District', 'Richmond District'): 11,
    ('Marina District', 'Pacific Heights'): 7,
}

# Initial conditions
start_location = 'Richmond District'
start_time_min = 9 * 60  # 9:00 AM in minutes

best_itinerary = []
max_met = 0

# Check all permutations of friends
for perm in permutations(friends):
    current_time = start_time_min
    current_location = start_location
    itinerary = []
    met_count = 0
    valid = True
    
    for friend in perm:
        # Calculate travel time
        travel_key = (current_location, friend['location'])
        if travel_key not in travel_time:
            valid = False
            break
        travel_duration = travel_time[travel_key]
        current_time += travel_duration
        
        # Determine earliest possible meeting start time
        meeting_start = max(current_time, friend['available_start'])
        
        # Check if meeting can fit within available time
        if meeting_start + friend['required_duration'] > friend['available_end']:
            valid = False
            break
        
        # Record the meeting
        meeting_end = meeting_start + friend['required_duration']
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': meeting_start,
            'end_time': meeting_end
        })
        met_count += 1
        
        # Update current time and location
        current_time = meeting_end
        current_location = friend['location']
    
    if valid and met_count > max_met:
        max_met = met_count
        best_itinerary = itinerary

# Convert the best itinerary to the required format
output_itinerary = []
for item in best_itinerary:
    output_item = {
        'action': 'meet',
        'location': item['location'],
        'person': item['person'],
        'start_time': minutes_to_time_str(item['start_time']),
        'end_time': minutes_to_time_str(item['end_time'])
    }
    output_itinerary.append(output_item)

# Create the final JSON output
result = {"itinerary": output_itinerary}

# Print the JSON-formatted result
print(json.dumps(result, indent=2))