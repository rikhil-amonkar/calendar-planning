import itertools

travel_times = {
    ('Nob Hill', 'North Beach'): 8,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Bayview'): 19,
    ('North Beach', 'Nob Hill'): 7,
    ('North Beach', 'Fisherman\'s Wharf'): 5,
    ('North Beach', 'Bayview'): 22,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'North Beach'): 6,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
    ('Bayview', 'Nob Hill'): 20,
    ('Bayview', 'North Beach'): 21,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
}

friends = [
    {
        'name': 'Helen',
        'location': 'North Beach',
        'start': 420,  # 7:00 AM
        'end': 1050,   # 17:45 (4:45 PM)
        'duration': 120
    },
    {
        'name': 'Kimberly',
        'location': 'Fisherman\'s Wharf',
        'start': 990,   # 16:30 (4:30 PM)
        'end': 1260,   # 21:00 (9:00 PM)
        'duration': 45
    },
    {
        'name': 'Patricia',
        'location': 'Bayview',
        'start': 1080, # 18:00 (6:00 PM)
        'end': 1290,  # 21:15 (9:15 PM)
        'duration': 120
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
    current_location = 'Nob Hill'
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