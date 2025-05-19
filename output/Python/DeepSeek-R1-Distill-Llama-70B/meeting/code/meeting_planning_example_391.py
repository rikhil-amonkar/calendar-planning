import itertools
import json

travel_times = {
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Financial District'): 30,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Presidio'): 18,
    ('Alamo Square', 'Financial District'): 17,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Financial District'): 11,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Alamo Square'): 18,
    ('Presidio', 'Russian Hill'): 14,
    ('Presidio', 'Financial District'): 23,
    ('Financial District', 'Sunset District'): 31,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'Russian Hill'): 10,
    ('Financial District', 'Presidio'): 22,
}

friends = [
    {
        'name': 'Kevin',
        'location': 'Alamo Square',
        'start': 495,  # 8:15 AM
        'end': 1410,   # 23:30 (9:30 PM)
        'duration': 75
    },
    {
        'name': 'Kimberly',
        'location': 'Russian Hill',
        'start': 570,  # 9:30 AM
        'end': 750,    # 12:30 PM
        'duration': 30
    },
    {
        'name': 'Joseph',
        'location': 'Presidio',
        'start': 1140, # 19:00 (7:00 PM)
        'end': 1215,  # 20:15 (8:15 PM)
        'duration': 45
    },
    {
        'name': 'Thomas',
        'location': 'Financial District',
        'start': 1260, # 21:00 (9:00 PM)
        'end': 1415,  # 23:45 (11:45 PM)
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

print(json.dumps(output))