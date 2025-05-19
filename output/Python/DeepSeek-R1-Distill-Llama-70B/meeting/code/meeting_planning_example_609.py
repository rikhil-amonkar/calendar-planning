import itertools
import json

# Travel times in minutes between locations
travel_times = {
    'Chinatown': {
        'Mission District': 18,
        'Alamo Square': 17,
        'Pacific Heights': 10,
        'Union Square': 7,
        'Golden Gate Park': 23,
        'Sunset District': 29,
        'Presidio': 19,
    },
    'Mission District': {
        'Chinatown': 16,
        'Alamo Square': 11,
        'Pacific Heights': 16,
        'Union Square': 15,
        'Golden Gate Park': 17,
        'Sunset District': 24,
        'Presidio': 25,
    },
    'Alamo Square': {
        'Chinatown': 16,
        'Mission District': 10,
        'Pacific Heights': 10,
        'Union Square': 14,
        'Golden Gate Park': 9,
        'Sunset District': 16,
        'Presidio': 18,
    },
    'Pacific Heights': {
        'Chinatown': 11,
        'Mission District': 15,
        'Alamo Square': 10,
        'Union Square': 12,
        'Golden Gate Park': 15,
        'Sunset District': 21,
        'Presidio': 11,
    },
    'Union Square': {
        'Chinatown': 7,
        'Mission District': 14,
        'Alamo Square': 15,
        'Pacific Heights': 15,
        'Golden Gate Park': 22,
        'Sunset District': 26,
        'Presidio': 24,
    },
    'Golden Gate Park': {
        'Chinatown': 23,
        'Mission District': 17,
        'Alamo Square': 9,
        'Pacific Heights': 16,
        'Union Square': 22,
        'Sunset District': 10,
        'Presidio': 11,
    },
    'Sunset District': {
        'Chinatown': 30,
        'Mission District': 24,
        'Alamo Square': 17,
        'Pacific Heights': 21,
        'Union Square': 30,
        'Golden Gate Park': 11,
        'Presidio': 16,
    },
    'Presidio': {
        'Chinatown': 21,
        'Mission District': 26,
        'Alamo Square': 18,
        'Pacific Heights': 11,
        'Union Square': 22,
        'Golden Gate Park': 12,
        'Sunset District': 15,
    }
}

# Friends' data
friends = [
    {
        'name': 'David',
        'location': 'Mission District',
        'start': '8:00',
        'end': '19:45',
        'duration': 45,
    },
    {
        'name': 'Kenneth',
        'location': 'Alamo Square',
        'start': '14:00',
        'end': '19:45',
        'duration': 120,
    },
    {
        'name': 'John',
        'location': 'Pacific Heights',
        'start': '17:00',
        'end': '20:00',
        'duration': 15,
    },
    {
        'name': 'Charles',
        'location': 'Union Square',
        'start': '21:45',
        'end': '22:45',
        'duration': 60,
    },
    {
        'name': 'Deborah',
        'location': 'Golden Gate Park',
        'start': '7:00',
        'end': '18:15',
        'duration': 90,
    },
    {
        'name': 'Karen',
        'location': 'Sunset District',
        'start': '17:45',
        'end': '21:15',
        'duration': 15,
    },
    {
        'name': 'Carol',
        'location': 'Presidio',
        'start': '8:15',
        'end': '9:15',
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
    current_location = 'Chinatown'
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