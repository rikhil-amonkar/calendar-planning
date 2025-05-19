import itertools
import json

# Travel times in minutes between locations
travel_times = {
    'Russian Hill': {
        'Nob Hill': 5,
        'Mission District': 16,
        'Embarcadero': 8,
    },
    'Nob Hill': {
        'Russian Hill': 5,
        'Mission District': 13,
        'Embarcadero': 9,
    },
    'Mission District': {
        'Russian Hill': 15,
        'Nob Hill': 12,
        'Embarcadero': 19,
    },
    'Embarcadero': {
        'Russian Hill': 8,
        'Nob Hill': 10,
        'Mission District': 20,
    }
}

# Friends' data
friends = [
    {
        'name': 'Patricia',
        'location': 'Nob Hill',
        'start': '18:30',
        'end': '21:45',
        'duration': 90,
    },
    {
        'name': 'Ashley',
        'location': 'Mission District',
        'start': '20:30',
        'end': '21:15',
        'duration': 45,
    },
    {
        'name': 'Timothy',
        'location': 'Embarcadero',
        'start': '9:45',
        'end': '17:45',
        'duration': 120,
    },
]

best_itinerary = []

# Convert time strings to minutes
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

# Try all possible permutations of friends
for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Russian Hill'
    temp_itinerary = []
    
    for friend in perm:
        # Convert friend's time window to minutes
        start = time_to_minutes(friend['start'])
        end = time_to_minutes(friend['end'])
        
        # Get travel time from current_location to friend's location
        if current_location not in travel_times or friend['location'] not in travel_times[current_location]:
            break  # No path available
        
        travel = travel_times[current_location][friend['location']]
        arrival = current_time + travel
        
        # Determine meeting start time
        meeting_start = max(arrival, start)
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end > end:
            break  # Cannot meet this friend
        
        # Add to temporary itinerary
        temp_itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': f"{meeting_start // 60}:{meeting_start % 60:02d}",
            'end_time': f"{meeting_end // 60}:{meeting_end % 60:02d}"
        })
        
        # Update current time and location
        current_time = meeting_end
        current_location = friend['location']
    
    # Update best itinerary if this permutation is better
    if len(temp_itinerary) > len(best_itinerary):
        best_itinerary = temp_itinerary

# Prepare the result
result = {
    "itinerary": best_itinerary
}

# Print the result as JSON
print(json.dumps(result))