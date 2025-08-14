import itertools
import json

def convert_time(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins}"

# Define travel times between locations
travel_times = {
    'Sunset District': {
        'Russian Hill': 24,
        'Chinatown': 30,
        'Presidio': 16,
        'Fisherman\'s Wharf': 29
    },
    'Russian Hill': {
        'Sunset District': 23,
        'Chinatown': 9,
        'Presidio': 14,
        'Fisherman\'s Wharf': 7
    },
    'Chinatown': {
        'Sunset District': 29,
        'Russian Hill': 7,
        'Presidio': 19,
        'Fisherman\'s Wharf': 8
    },
    'Presidio': {
        'Sunset District': 15,
        'Russian Hill': 14,
        'Chinatown': 21,
        'Fisherman\'s Wharf': 19
    },
    'Fisherman\'s Wharf': {
        'Sunset District': 27,
        'Russian Hill': 7,
        'Chinatown': 12,
        'Presidio': 17
    }
}

# Define friends with their constraints
friends = [
    {
        'name': 'Michelle',
        'location': 'Chinatown',
        'available_start': convert_time('8:15'),
        'available_end': convert_time('14:00'),
        'required_duration': 15
    },
    {
        'name': 'William',
        'location': 'Russian Hill',
        'available_start': convert_time('18:30'),
        'available_end': convert_time('20:45'),
        'required_duration': 105
    },
    {
        'name': 'George',
        'location': 'Presidio',
        'available_start': convert_time('10:30'),
        'available_end': convert_time('18:45'),
        'required_duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Fisherman\'s Wharf',
        'available_start': convert_time('9:00'),
        'available_end': convert_time('13:45'),
        'required_duration': 30
    }
]

def is_valid_permutation(perm):
    current_time = convert_time('9:00')  # Start at 9:00 AM
    current_location = 'Sunset District'
    for friend in perm:
        # Check if travel time exists
        if friend['location'] not in travel_times[current_location]:
            return False
        
        # Calculate arrival time at friend's location
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        
        # Determine meeting start time (max of arrival time and friend's available start)
        meeting_start = max(arrival_time, friend['available_start'])
        
        # Check if meeting can be completed within friend's available time
        meeting_end = meeting_start + friend['required_duration']
        if meeting_end > friend['available_end']:
            return False
        
        # Update current time and location
        current_time = meeting_end
        current_location = friend['location']
    
    return True

def generate_itinerary(perm):
    current_time = convert_time('9:00')
    current_location = 'Sunset District'
    itinerary = []
    
    for friend in perm:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        
        meeting_start = max(arrival_time, friend['available_start'])
        meeting_end = meeting_start + friend['required_duration']
        
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = friend['location']
    
    return itinerary

# Find the optimal itinerary
best_itinerary = None
max_meetings = 0

for r in range(4, 0, -1):
    for perm in itertools.permutations(friends, r):
        if is_valid_permutation(perm):
            if r > max_meetings:
                max_meetings = r
                best_itinerary = generate_itinerary(perm)
    if max_meetings == r:
        break

# Format and print the result
result = {
    "itinerary": best_itinerary or []
}

print(json.dumps(result, indent=2))