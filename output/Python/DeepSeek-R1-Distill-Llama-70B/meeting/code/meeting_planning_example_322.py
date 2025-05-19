import itertools

travel_times = {
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Fisherman\'s Wharf'): 29,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Chinatown'): 9,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Russian Hill'): 7,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Fisherman\'s Wharf'): 19,
    ('Fisherman\'s Wharf', 'Sunset District'): 27,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Presidio'): 17,
}

friends = [
    {
        'name': 'William',
        'location': 'Russian Hill',
        'start': 1170,  # 19:30 (7:30 PM)
        'end': 1305,    # 21:45 (8:45 PM)
        'duration': 105
    },
    {
        'name': 'Michelle',
        'location': 'Chinatown',
        'start': 495,    # 8:15 AM
        'end': 840,     # 14:00 (2:00 PM)
        'duration': 15
    },
    {
        'name': 'George',
        'location': 'Presidio',
        'start': 630,    # 10:30 AM
        'end': 1245,    # 20:45 (6:45 PM)
        'duration': 30
    },
    {
        'name': 'Robert',
        'location': 'Fisherman\'s Wharf',
        'start': 540,    # 9:00 AM
        'end': 765,     # 12:45 (1:45 PM)
        'duration': 30
    }
]

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours}:{mins:02d}"

best_itinerary = []
max_meetings = 0

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Sunset District'
    itinerary = []
    
    for friend in perm:
        travel = travel_times.get((current_location, friend['location']), None)
        if travel is None:
            continue
        
        arrival = current_time + travel
        meeting_start = max(arrival, friend['start'])
        meeting_end = meeting_start + friend['duration']
        
        if meeting_end > friend['end']:
            continue
        
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = friend['location']
    
    if len(itinerary) > max_meetings:
        max_meetings = len(itinerary)
        best_itinerary = itinerary

output = {
    "itinerary": best_itinerary
}

import json
print(json.dumps(output))