import itertools

travel_times = {
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Haight-Ashbury'): 21,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Financial District'): 5,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Haight-Ashbury', 'Embarcadero'): 20,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Bayview'): 18,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Financial District'): 21,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Golden Gate Park'): 22,
    ('Bayview', 'Haight-Ashbury'): 19,
    ('Bayview', 'Presidio'): 31,
    ('Bayview', 'Financial District'): 19,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Bayview'): 31,
    ('Presidio', 'Financial District'): 23,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Haight-Ashbury'): 19,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Presidio'): 22,
}

friends = [
    {
        'name': 'Mary',
        'location': 'Golden Gate Park',
        'start': 525,  # 8:45 AM
        'end': 705,    # 11:45 AM
        'duration': 45
    },
    {
        'name': 'Kevin',
        'location': 'Haight-Ashbury',
        'start': 615,  # 10:15 AM
        'end': 975,    # 16:15 (4:15 PM)
        'duration': 90
    },
    {
        'name': 'Deborah',
        'location': 'Bayview',
        'start': 1020, # 17:00 (5:00 PM)
        'end': 1350,  # 22:15 (10:15 PM)
        'duration': 120
    },
    {
        'name': 'Stephanie',
        'location': 'Presidio',
        'start': 600,  # 10:00 AM
        'end': 1035,  # 17:15 (5:15 PM)
        'duration': 120
    },
    {
        'name': 'Emily',
        'location': 'Financial District',
        'start': 690,  # 11:30 AM
        'end': 1410,  # 23:45 (11:45 PM)
        'duration': 105
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
    current_location = 'Embarcadero'
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