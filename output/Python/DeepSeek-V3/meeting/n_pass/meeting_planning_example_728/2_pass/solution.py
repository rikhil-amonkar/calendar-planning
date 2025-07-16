import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input data (same as before)
travel_times = {
    'Marina District': {
        'Mission District': 20,
        'Fisherman\'s Wharf': 10,
        'Presidio': 10,
        'Union Square': 16,
        'Sunset District': 19,
        'Financial District': 17,
        'Haight-Ashbury': 16,
        'Russian Hill': 8
    },
    'Mission District': {
        'Marina District': 19,
        'Fisherman\'s Wharf': 22,
        'Presidio': 25,
        'Union Square': 15,
        'Sunset District': 24,
        'Financial District': 15,
        'Haight-Ashbury': 12,
        'Russian Hill': 15
    },
    'Fisherman\'s Wharf': {
        'Marina District': 9,
        'Mission District': 22,
        'Presidio': 17,
        'Union Square': 13,
        'Sunset District': 27,
        'Financial District': 11,
        'Haight-Ashbury': 22,
        'Russian Hill': 7
    },
    'Presidio': {
        'Marina District': 11,
        'Mission District': 26,
        'Fisherman\'s Wharf': 19,
        'Union Square': 22,
        'Sunset District': 15,
        'Financial District': 23,
        'Haight-Ashbury': 15,
        'Russian Hill': 14
    },
    'Union Square': {
        'Marina District': 18,
        'Mission District': 14,
        'Fisherman\'s Wharf': 15,
        'Presidio': 24,
        'Sunset District': 27,
        'Financial District': 9,
        'Haight-Ashbury': 18,
        'Russian Hill': 13
    },
    'Sunset District': {
        'Marina District': 21,
        'Mission District': 25,
        'Fisherman\'s Wharf': 29,
        'Presidio': 16,
        'Union Square': 30,
        'Financial District': 30,
        'Haight-Ashbury': 15,
        'Russian Hill': 24
    },
    'Financial District': {
        'Marina District': 15,
        'Mission District': 17,
        'Fisherman\'s Wharf': 10,
        'Presidio': 22,
        'Union Square': 9,
        'Sunset District': 30,
        'Haight-Ashbury': 19,
        'Russian Hill': 11
    },
    'Haight-Ashbury': {
        'Marina District': 17,
        'Mission District': 11,
        'Fisherman\'s Wharf': 23,
        'Presidio': 15,
        'Union Square': 19,
        'Sunset District': 15,
        'Financial District': 21,
        'Russian Hill': 17
    },
    'Russian Hill': {
        'Marina District': 7,
        'Mission District': 16,
        'Fisherman\'s Wharf': 7,
        'Presidio': 14,
        'Union Square': 10,
        'Sunset District': 23,
        'Financial District': 11,
        'Haight-Ashbury': 17
    }
}

friends = [
    {'name': 'Karen', 'location': 'Mission District', 'start': '14:15', 'end': '22:00', 'duration': 30},
    {'name': 'Richard', 'location': 'Fisherman\'s Wharf', 'start': '14:30', 'end': '17:30', 'duration': 30},
    {'name': 'Robert', 'location': 'Presidio', 'start': '21:45', 'end': '22:45', 'duration': 60},
    {'name': 'Joseph', 'location': 'Union Square', 'start': '11:45', 'end': '14:45', 'duration': 120},
    {'name': 'Helen', 'location': 'Sunset District', 'start': '14:45', 'end': '20:45', 'duration': 105},
    {'name': 'Elizabeth', 'location': 'Financial District', 'start': '10:00', 'end': '12:45', 'duration': 75},
    {'name': 'Kimberly', 'location': 'Haight-Ashbury', 'start': '14:15', 'end': '17:30', 'duration': 105},
    {'name': 'Ashley', 'location': 'Russian Hill', 'start': '11:30', 'end': '21:30', 'duration': 45}
]

def generate_itinerary():
    current_location = 'Marina District'
    current_time = time_to_minutes('9:00')
    itinerary = []
    remaining_friends = friends.copy()
    
    # Sort friends by their time window (earlier end times first)
    remaining_friends.sort(key=lambda x: time_to_minutes(x['end']))
    
    while remaining_friends:
        best_friend = None
        best_arrival = None
        best_start = None
        best_end = None
        
        for friend in remaining_friends:
            # Calculate travel time
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time
            
            # Calculate possible meeting window
            meeting_start = max(arrival_time, time_to_minutes(friend['start']))
            meeting_end = meeting_start + friend['duration']
            
            # Check if meeting is possible
            if meeting_end <= time_to_minutes(friend['end']):
                # If this is the first valid friend or has earlier end time
                if best_friend is None or meeting_end < best_end:
                    best_friend = friend
                    best_arrival = arrival_time
                    best_start = meeting_start
                    best_end = meeting_end
        
        if best_friend is None:
            break  # No more meetings possible
        
        # Add to itinerary
        itinerary.append({
            'action': 'meet',
            'location': best_friend['location'],
            'person': best_friend['name'],
            'start_time': minutes_to_time(best_start),
            'end_time': minutes_to_time(best_end)
        })
        
        # Update current state
        current_location = best_friend['location']
        current_time = best_end
        remaining_friends.remove(best_friend)
    
    return itinerary

itinerary = generate_itinerary()
print(json.dumps({"itinerary": itinerary}, indent=2))