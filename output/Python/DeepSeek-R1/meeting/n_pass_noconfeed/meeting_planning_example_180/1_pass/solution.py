import json
import itertools

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(minutes_val):
    hours = minutes_val // 60
    minutes = minutes_val % 60
    return f"{hours}:{minutes:02d}"

# Define travel times as a dictionary
travel_times = {
    'North Beach': {
        'Mission District': 18,
        'The Castro': 22
    },
    'Mission District': {
        'North Beach': 17,
        'The Castro': 7
    },
    'The Castro': {
        'North Beach': 20,
        'Mission District': 7
    }
}

# Define constraints
start_location = 'North Beach'
start_time = time_to_minutes('9:00')

# Define friends with their constraints
friends = [
    {
        'name': 'James',
        'location': 'Mission District',
        'start_avail': time_to_minutes('12:45'),
        'end_avail': time_to_minutes('14:00'),
        'min_duration': 75
    },
    {
        'name': 'Robert',
        'location': 'The Castro',
        'start_avail': time_to_minutes('12:45'),
        'end_avail': time_to_minutes('15:15'),
        'min_duration': 30
    }
]

# Generate all permutations of friends
permutations = list(itertools.permutations(friends))
best_count = -1
best_itinerary_minutes = None

# Evaluate each permutation
for perm in permutations:
    current_time = start_time
    current_loc = start_location
    itinerary = []
    count = 0
    for friend in perm:
        # Get travel time to friend's location
        travel_time = travel_times[current_loc][friend['location']]
        arrival_time = current_time + travel_time
        
        # Start meeting at the later of arrival or friend's availability
        start_meeting = max(arrival_time, friend['start_avail'])
        
        # Check if meeting is possible
        if start_meeting > friend['end_avail']:
            break
            
        end_meeting = start_meeting + friend['min_duration']
        if end_meeting > friend['end_avail']:
            break
            
        # Add meeting to itinerary (in minutes for now)
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': start_meeting,
            'end_time': end_meeting
        })
        
        # Update current time and location
        current_time = end_meeting
        current_loc = friend['location']
        count += 1
    
    # Update best itinerary if this permutation has more meetings
    if count > best_count:
        best_count = count
        best_itinerary_minutes = itinerary

# Convert times in best itinerary to formatted strings
if best_itinerary_minutes:
    best_itinerary = []
    for event in best_itinerary_minutes:
        event_copy = event.copy()
        event_copy['start_time'] = minutes_to_time(event['start_time'])
        event_copy['end_time'] = minutes_to_time(event['end_time'])
        best_itinerary.append(event_copy)
else:
    best_itinerary = []

# Output the result as JSON
result = {"itinerary": best_itinerary}
print(json.dumps(result))