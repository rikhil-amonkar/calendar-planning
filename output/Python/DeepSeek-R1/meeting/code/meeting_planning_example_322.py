import itertools
import json

friends_data = [
    {
        'name': 'Michelle',
        'location': 'Chinatown',
        'start': 8 * 60 + 15,
        'end': 14 * 60 + 0,
        'duration': 15
    },
    {
        'name': 'Robert',
        'location': 'Fisherman\'s Wharf',
        'start': 9 * 60 + 0,
        'end': 13 * 60 + 45,
        'duration': 30
    },
    {
        'name': 'George',
        'location': 'Presidio',
        'start': 10 * 60 + 30,
        'end': 18 * 60 + 45,
        'duration': 30
    },
    {
        'name': 'William',
        'location': 'Russian Hill',
        'start': 18 * 60 + 30,
        'end': 20 * 60 + 45,
        'duration': 105
    }
]

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

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

non_william = [f for f in friends_data if f['name'] != 'William']
william = [f for f in friends_data if f['name'] == 'William'][0]
best_itinerary = None
max_met = 0

for perm in itertools.permutations(non_william):
    candidate_order = list(perm) + [william]
    current_location = 'Sunset District'
    current_time = 9 * 60
    itinerary = []
    valid = True
    
    for friend in candidate_order:
        travel_duration = travel_times[current_location].get(friend['location'])
        if travel_duration is None:
            valid = False
            break
        arrival_time = current_time + travel_duration
        start_meeting = max(arrival_time, friend['start'])
        end_meeting = start_meeting + friend['duration']
        
        if end_meeting > friend['end']:
            valid = False
            break
        
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': time_to_str(start_meeting),
            'end_time': time_to_str(end_meeting)
        })
        
        current_time = end_meeting
        current_location = friend['location']
    
    if valid and len(candidate_order) > max_met:
        max_met = len(candidate_order)
        best_itinerary = itinerary.copy()

if best_itinerary is None:
    for perm in itertools.permutations(non_william):
        current_location = 'Sunset District'
        current_time = 9 * 60
        itinerary = []
        valid = True
        
        for friend in perm:
            travel_duration = travel_times[current_location].get(friend['location'])
            if travel_duration is None:
                valid = False
                break
            arrival_time = current_time + travel_duration
            start_meeting = max(arrival_time, friend['start'])
            end_meeting = start_meeting + friend['duration']
            
            if end_meeting > friend['end']:
                valid = False
                break
            
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': time_to_str(start_meeting),
                'end_time': time_to_str(end_meeting)
            })
            
            current_time = end_meeting
            current_location = friend['location']
        
        if valid and len(perm) > max_met:
            max_met = len(perm)
            best_itinerary = itinerary.copy()

print(json.dumps({"itinerary": best_itinerary}, indent=2))