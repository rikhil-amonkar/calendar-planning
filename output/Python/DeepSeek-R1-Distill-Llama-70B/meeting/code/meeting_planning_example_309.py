import itertools

travel_times = {
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Fisherman\'s Wharf'): 10,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Bayview'): 22,
    ('Chinatown', 'Fisherman\'s Wharf'): 8,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'Chinatown'): 16,
    ('Alamo Square', 'Bayview'): 16,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Chinatown'): 18,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Fisherman\'s Wharf'): 25,
    ('Fisherman\'s Wharf', 'Financial District'): 11,
    ('Fisherman\'s Wharf', 'Chinatown'): 12,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'Bayview'): 26,
}

friends = [
    {
        'name': 'Nancy',
        'location': 'Chinatown',
        'start': 570,  # 9:30 AM
        'end': 810,    # 13:30 (1:30 PM)
        'duration': 90
    },
    {
        'name': 'Mary',
        'location': 'Alamo Square',
        'start': 420,  # 7:00 AM
        'end': 1080,   # 18:00 (6:00 PM)
        'duration': 75
    },
    {
        'name': 'Jessica',
        'location': 'Bayview',
        'start': 675,  # 11:15 AM
        'end': 780,    # 13:00 (1:00 PM)
        'duration': 45
    },
    {
        'name': 'Rebecca',
        'location': 'Fisherman\'s Wharf',
        'start': 420,  # 7:00 AM
        'end': 510,    # 8:30 AM
        'duration': 45
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
    current_location = 'Financial District'
    itinerary = []
    
    for friend in perm:
        if friend['name'] == 'Rebecca':
            continue  # Skip Rebecca as she's not available after 8:30 AM
        
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