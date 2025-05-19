import itertools
import json

# Travel times in minutes between locations
travel_times = {
    'Nob Hill': {
        'Presidio': 17,
        'North Beach': 8,
        'Fisherman\'s Wharf': 11,
        'Pacific Heights': 8,
    },
    'Presidio': {
        'Nob Hill': 18,
        'North Beach': 18,
        'Fisherman\'s Wharf': 19,
        'Pacific Heights': 11,
    },
    'North Beach': {
        'Nob Hill': 7,
        'Presidio': 17,
        'Fisherman\'s Wharf': 5,
        'Pacific Heights': 8,
    },
    'Fisherman\'s Wharf': {
        'Nob Hill': 11,
        'Presidio': 17,
        'North Beach': 6,
        'Pacific Heights': 12,
    },
    'Pacific Heights': {
        'Nob Hill': 8,
        'Presidio': 11,
        'North Beach': 9,
        'Fisherman\'s Wharf': 13,
    }
}

# Friends' data
friends = [
    {
        'name': 'Jeffrey',
        'location': 'Presidio',
        'start': '8:00',
        'end': '10:00',
        'duration': 105,
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'start': '13:30',
        'end': '22:00',
        'duration': 45,
    },
    {
        'name': 'Barbara',
        'location': 'Fisherman\'s Wharf',
        'start': '18:00',
        'end': '21:30',
        'duration': 30,
    },
    {
        'name': 'John',
        'location': 'Pacific Heights',
        'start': '9:00',
        'end': '13:30',
        'duration': 15,
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
    current_location = 'Nob Hill'
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