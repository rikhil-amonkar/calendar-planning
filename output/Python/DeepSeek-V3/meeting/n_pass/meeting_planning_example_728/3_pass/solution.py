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

def generate_best_itinerary():
    best_itinerary = []
    max_meetings = 0
    
    # Try different orders of friends to maximize meetings
    for friend_order in permutations(friends[:5]):  # Limit permutations for performance
        current_location = 'Marina District'
        current_time = time_to_minutes('9:00')
        itinerary = []
        remaining_friends = list(friend_order) + friends[5:]  # Keep later friends in original order
        
        for friend in remaining_friends:
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time
            meeting_start = max(arrival_time, time_to_minutes(friend['start']))
            meeting_end = meeting_start + friend['duration']
            
            if meeting_end <= time_to_minutes(friend['end']):
                itinerary.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                current_location = friend['location']
                current_time = meeting_end
        
        if len(itinerary) > max_meetings:
            max_meetings = len(itinerary)
            best_itinerary = itinerary
            if max_meetings == len(friends):
                break  # Found optimal solution
    
    return best_itinerary

itinerary = generate_best_itinerary()
print(json.dumps({"itinerary": itinerary}, indent=2))