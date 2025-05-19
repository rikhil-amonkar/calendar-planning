import itertools
import json

# Travel times in minutes between locations
travel_times = {
    'Pacific Heights': {
        'North Beach': 9,
        'Financial District': 13,
        'Alamo Square': 10,
        'Mission District': 15,
    },
    'North Beach': {
        'Pacific Heights': 8,
        'Financial District': 8,
        'Alamo Square': 16,
        'Mission District': 18,
    },
    'Financial District': {
        'Pacific Heights': 13,
        'North Beach': 7,
        'Alamo Square': 17,
        'Mission District': 17,
    },
    'Alamo Square': {
        'Pacific Heights': 10,
        'North Beach': 15,
        'Financial District': 17,
        'Mission District': 10,
    },
    'Mission District': {
        'Pacific Heights': 16,
        'North Beach': 17,
        'Financial District': 17,
        'Alamo Square': 11,
    }
}

# Friends' data
friends = [
    {
        'name': 'Helen',
        'location': 'North Beach',
        'start': '9:00',
        'end': '17:00',
        'duration': 15,
    },
    {
        'name': 'Betty',
        'location': 'Financial District',
        'start': '19:00',
        'end': '21:45',
        'duration': 90,
    },
    {
        'name': 'Amanda',
        'location': 'Alamo Square',
        'start': '19:45',
        'end': '21:00',
        'duration': 60,
    },
    {
        'name': 'Kevin',
        'location': 'Mission District',
        'start': '10:45',
        'end': '14:45',
        'duration': 45,
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
    current_location = 'Pacific Heights'
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