import itertools
import json

# Travel times in minutes between locations
travel_times = {
    'Golden Gate Park': {
        'Alamo Square': 10,
        'Presidio': 11,
        'Russian Hill': 19,
    },
    'Alamo Square': {
        'Golden Gate Park': 9,
        'Presidio': 18,
        'Russian Hill': 13,
    },
    'Presidio': {
        'Golden Gate Park': 12,
        'Alamo Square': 18,
        'Russian Hill': 14,
    },
    'Russian Hill': {
        'Golden Gate Park': 21,
        'Alamo Square': 15,
        'Presidio': 14,
    }
}

# Friends' data
friends = [
    {
        'name': 'Timothy',
        'location': 'Alamo Square',
        'start': '12:00',
        'end': '16:15',
        'duration': 105,
    },
    {
        'name': 'Mark',
        'location': 'Presidio',
        'start': '18:45',
        'end': '21:00',
        'duration': 60,
    },
    {
        'name': 'Joseph',
        'location': 'Russian Hill',
        'start': '16:45',
        'end': '21:30',
        'duration': 60,
    },
]

best_itinerary = []

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Try all possible permutations of friends
for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM in minutes
    current_location = 'Golden Gate Park'
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
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
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