import itertools
import json

# Travel times in minutes between locations
travel_times = {
    'Bayview': {
        'Nob Hill': 20,
        'Union Square': 17,
        'Chinatown': 18,
        'The Castro': 20,
        'Presidio': 31,
        'Pacific Heights': 23,
        'Russian Hill': 23,
    },
    'Nob Hill': {
        'Bayview': 19,
        'Union Square': 7,
        'Chinatown': 6,
        'The Castro': 17,
        'Presidio': 17,
        'Pacific Heights': 8,
        'Russian Hill': 5,
    },
    'Union Square': {
        'Bayview': 15,
        'Nob Hill': 9,
        'Chinatown': 7,
        'The Castro': 19,
        'Presidio': 24,
        'Pacific Heights': 15,
        'Russian Hill': 13,
    },
    'Chinatown': {
        'Bayview': 22,
        'Nob Hill': 8,
        'Union Square': 7,
        'The Castro': 22,
        'Presidio': 19,
        'Pacific Heights': 10,
        'Russian Hill': 7,
    },
    'The Castro': {
        'Bayview': 19,
        'Nob Hill': 16,
        'Union Square': 19,
        'Chinatown': 20,
        'Presidio': 20,
        'Pacific Heights': 16,
        'Russian Hill': 18,
    },
    'Presidio': {
        'Bayview': 31,
        'Nob Hill': 18,
        'Union Square': 22,
        'Chinatown': 21,
        'The Castro': 21,
        'Pacific Heights': 11,
        'Russian Hill': 14,
    },
    'Pacific Heights': {
        'Bayview': 22,
        'Nob Hill': 8,
        'Union Square': 12,
        'Chinatown': 11,
        'The Castro': 16,
        'Presidio': 11,
        'Russian Hill': 7,
    },
    'Russian Hill': {
        'Bayview': 23,
        'Nob Hill': 5,
        'Union Square': 11,
        'Chinatown': 9,
        'The Castro': 21,
        'Presidio': 14,
        'Pacific Heights': 7,
    }
}

# Friends' data
friends = [
    {
        'name': 'Paul',
        'location': 'Nob Hill',
        'start': '16:15',
        'end': '21:15',
        'duration': 60,
    },
    {
        'name': 'Carol',
        'location': 'Union Square',
        'start': '18:00',
        'end': '20:15',
        'duration': 120,
    },
    {
        'name': 'Patricia',
        'location': 'Chinatown',
        'start': '20:00',
        'end': '21:30',
        'duration': 75,
    },
    {
        'name': 'Karen',
        'location': 'The Castro',
        'start': '17:00',
        'end': '19:00',
        'duration': 45,
    },
    {
        'name': 'Nancy',
        'location': 'Presidio',
        'start': '11:45',
        'end': '22:00',
        'duration': 30,
    },
    {
        'name': 'Jeffrey',
        'location': 'Pacific Heights',
        'start': '20:00',
        'end': '20:45',
        'duration': 45,
    },
    {
        'name': 'Matthew',
        'location': 'Russian Hill',
        'start': '15:45',
        'end': '21:45',
        'duration': 75,
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
    current_location = 'Bayview'
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