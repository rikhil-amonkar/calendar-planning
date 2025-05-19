import itertools
import json

# Travel times in minutes between locations
travel_times = {
    'The Castro': {
        'Mission District': 7,
        'Financial District': 20,
    },
    'Mission District': {
        'The Castro': 7,
        'Financial District': 17,
    },
    'Financial District': {
        'The Castro': 23,
        'Mission District': 17,
    }
}

# Friends' data
friends = [
    {
        'name': 'Laura',
        'location': 'Mission District',
        'start': '12:15',
        'end': '19:45',
        'duration': 75,
    },
    {
        'name': 'Anthony',
        'location': 'Financial District',
        'start': '12:30',
        'end': '14:45',
        'duration': 30,
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
    current_location = 'The Castro'
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