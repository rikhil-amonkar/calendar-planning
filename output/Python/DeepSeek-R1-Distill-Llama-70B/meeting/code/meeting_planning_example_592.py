import itertools
import json

# Travel times in minutes between locations
travel_times = {
    'North Beach': {
        'Pacific Heights': 8,
        'Chinatown': 6,
        'Union Square': 7,
        'Mission District': 18,
        'Golden Gate Park': 22,
        'Nob Hill': 7,
    },
    'Pacific Heights': {
        'North Beach': 9,
        'Chinatown': 11,
        'Union Square': 12,
        'Mission District': 15,
        'Golden Gate Park': 15,
        'Nob Hill': 8,
    },
    'Chinatown': {
        'North Beach': 3,
        'Pacific Heights': 10,
        'Union Square': 7,
        'Mission District': 18,
        'Golden Gate Park': 23,
        'Nob Hill': 8,
    },
    'Union Square': {
        'North Beach': 10,
        'Pacific Heights': 15,
        'Chinatown': 7,
        'Mission District': 14,
        'Golden Gate Park': 22,
        'Nob Hill': 9,
    },
    'Mission District': {
        'North Beach': 17,
        'Pacific Heights': 16,
        'Chinatown': 16,
        'Union Square': 15,
        'Golden Gate Park': 17,
        'Nob Hill': 12,
    },
    'Golden Gate Park': {
        'North Beach': 24,
        'Pacific Heights': 16,
        'Chinatown': 23,
        'Union Square': 22,
        'Mission District': 17,
        'Nob Hill': 20,
    },
    'Nob Hill': {
        'North Beach': 8,
        'Pacific Heights': 8,
        'Chinatown': 6,
        'Union Square': 7,
        'Mission District': 13,
        'Golden Gate Park': 17,
    }
}

# Friends' data
friends = [
    {
        'name': 'James',
        'location': 'Pacific Heights',
        'start': '20:00',
        'end': '22:00',
        'duration': 120,
    },
    {
        'name': 'Robert',
        'location': 'Chinatown',
        'start': '12:15',
        'end': '16:45',
        'duration': 90,
    },
    {
        'name': 'Jeffrey',
        'location': 'Union Square',
        'start': '9:30',
        'end': '15:30',
        'duration': 120,
    },
    {
        'name': 'Carol',
        'location': 'Mission District',
        'start': '18:15',
        'end': '21:15',
        'duration': 15,
    },
    {
        'name': 'Mark',
        'location': 'Golden Gate Park',
        'start': '11:30',
        'end': '17:45',
        'duration': 15,
    },
    {
        'name': 'Sandra',
        'location': 'Nob Hill',
        'start': '8:00',
        'end': '15:30',
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
    current_location = 'North Beach'
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