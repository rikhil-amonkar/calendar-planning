import itertools

# Travel times in minutes between locations
travel_times = {
    'Presidio': {
        'Golden Gate Park': 12,
        'Bayview': 31,
        'Chinatown': 21,
        'North Beach': 18,
        'Mission District': 26,
    },
    'Golden Gate Park': {
        'Presidio': 11,
        'Bayview': 23,
        'Chinatown': 23,
        'North Beach': 24,
        'Mission District': 17,
    },
    'Bayview': {
        'Presidio': 31,
        'Golden Gate Park': 22,
        'Chinatown': 18,
        'North Beach': 21,
        'Mission District': 13,
    },
    'Chinatown': {
        'Presidio': 19,
        'Golden Gate Park': 23,
        'Bayview': 22,
        'North Beach': 3,
        'Mission District': 18,
    },
    'North Beach': {
        'Presidio': 17,
        'Golden Gate Park': 22,
        'Bayview': 22,
        'Chinatown': 6,
        'Mission District': 17,
    },
    'Mission District': {
        'Presidio': 25,
        'Golden Gate Park': 17,
        'Bayview': 15,
        'Chinatown': 16,
        'North Beach': 17,
    }
}

# Friends' data
friends = [
    {
        'name': 'Daniel',
        'location': 'Mission District',
        'start': '7:00',
        'end': '11:15',
        'duration': 105,
    },
    {
        'name': 'Ronald',
        'location': 'Chinatown',
        'start': '7:15',
        'end': '14:45',
        'duration': 90,
    },
    {
        'name': 'Jessica',
        'location': 'Golden Gate Park',
        'start': '13:45',
        'end': '15:00',
        'duration': 30,
    },
    {
        'name': 'William',
        'location': 'North Beach',
        'start': '13:15',
        'end': '20:15',
        'duration': 15,
    },
    {
        'name': 'Ashley',
        'location': 'Bayview',
        'start': '17:15',
        'end': '20:00',
        'duration': 105,
    },
]

best_itinerary = []

# Try all possible permutations of friends
for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Presidio'
    temp_itinerary = []
    
    for friend in perm:
        # Get travel time from current_location to friend's location
        if current_location not in travel_times or friend['location'] not in travel_times[current_location]:
            break  # No path available
        
        travel = travel_times[current_location][friend['location']]
        arrival = current_time + travel
        
        # Convert friend's time window to minutes
        start_h, start_m = map(int, friend['start'].split(':'))
        start = start_h * 60 + start_m
        end_h, end_m = map(int, friend['end'].split(':'))
        end = end_h * 60 + end_m
        
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
import json
print(json.dumps(result))