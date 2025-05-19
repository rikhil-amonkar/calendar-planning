import itertools

travel_times = {
    ('Golden Gate Park', 'Fisherman's Wharf'): 24,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Fisherman's Wharf', 'Golden Gate Park'): 25,
    ('Fisherman's Wharf', 'Bayview'): 26,
    ('Fisherman's Wharf', 'Mission District'): 22,
    ('Fisherman's Wharf', 'Embarcadero'): 8,
    ('Fisherman's Wharf', 'Financial District'): 11,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Fisherman's Wharf'): 25,
    ('Bayview', 'Mission District'): 13,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Financial District'): 19,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Fisherman's Wharf'): 22,
    ('Mission District', 'Bayview'): 15,
    ('Mission District', 'Embarcadero'): 19,
    ('Mission District', 'Financial District'): 17,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Fisherman's Wharf'): 6,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Mission District'): 20,
    ('Embarcadero', 'Financial District'): 5,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Fisherman's Wharf'): 10,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Mission District'): 17,
    ('Financial District', 'Embarcadero'): 4,
}

friends = [
    {
        'name': 'Joseph',
        'location': 'Fisherman's Wharf',
        'start': 480,
        'end': 1050,
        'duration': 90
    },
    {
        'name': 'Jeffrey',
        'location': 'Bayview',
        'start': 1050,
        'end': 1170,
        'duration': 60
    },
    {
        'name': 'Kevin',
        'location': 'Mission District',
        'start': 675,
        'end': 915,
        'duration': 30
    },
    {
        'name': 'Barbara',
        'location': 'Financial District',
        'start': 630,
        'end': 990,
        'duration': 15
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
    current_location = 'Golden Gate Park'
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