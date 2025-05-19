import itertools
import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('The Castro', 'Presidio'): 20,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('The Castro', 'Mission District'): 7,
    ('The Castro', 'Golden Gate Park'): 11,
    ('The Castro', 'Russian Hill'): 18,
    ('Presidio', 'The Castro'): 21,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Haight-Ashbury'): 15,
    ('Presidio', 'Mission District'): 26,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Russian Hill'): 14,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Russian Hill'): 24,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Presidio'): 15,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Mission District', 'The Castro'): 7,
    ('Mission District', 'Presidio'): 25,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Mission District', 'Russian Hill'): 15,
    ('Golden Gate Park', 'The Castro'): 13,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Presidio'): 14,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Mission District'): 16,
    ('Russian Hill', 'Golden Gate Park'): 21,
}

friends = [
    {
        'location': 'Presidio',
        'name': 'Rebecca',
        'start': 1115,  # 6:15 PM
        'end': 1265,    # 8:45 PM
        'duration': 60
    },
    {
        'location': 'Sunset District',
        'name': 'Linda',
        'start': 1020,  # 3:30 PM
        'end': 1395,    # 7:45 PM
        'duration': 30
    },
    {
        'location': 'Haight-Ashbury',
        'name': 'Elizabeth',
        'start': 1175,  # 5:15 PM
        'end': 1350,    # 7:30 PM
        'duration': 105
    },
    {
        'location': 'Mission District',
        'name': 'William',
        'start': 735,    # 1:15 PM
        'end': 1350,    # 7:30 PM
        'duration': 30
    },
    {
        'location': 'Golden Gate Park',
        'name': 'Robert',
        'start': 855,    # 2:15 PM
        'end': 1710,    # 9:30 PM
        'duration': 45
    },
    {
        'location': 'Russian Hill',
        'name': 'Mark',
        'start': 600,    # 10:00 AM
        'end': 1715,    # 9:15 PM
        'duration': 75
    }
]

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'The Castro'
    itinerary = []
    valid = True
    
    for friend in perm:
        travel = travel_times.get((current_location, friend['location']), None)
        if travel is None:
            valid = False
            break
        arrival = current_time + travel
        meeting_start = max(arrival, friend['start'])
        meeting_end = meeting_start + friend['duration']
        if meeting_end > friend['end']:
            valid = False
            break
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': format_time(meeting_start),
            'end_time': format_time(meeting_end)
        })
        current_time = meeting_end
        current_location = friend['location']
    
    if valid and len(itinerary) == 6:
        print(json.dumps({'itinerary': itinerary}))
        exit()

# If no permutation meets all six, check for permutations with fewer friends
max_meetings = 0
best_itinerary = []
for r in range(5, 0, -1):
    for perm in itertools.permutations(friends, r):
        current_time = 540
        current_location = 'The Castro'
        itinerary = []
        valid = True
        
        for friend in perm:
            travel = travel_times.get((current_location, friend['location']), None)
            if travel is None:
                valid = False
                break
            arrival = current_time + travel
            meeting_start = max(arrival, friend['start'])
            meeting_end = meeting_start + friend['duration']
            if meeting_end > friend['end']:
                valid = False
                break
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': format_time(meeting_start),
                'end_time': format_time(meeting_end)
            })
            current_time = meeting_end
            current_location = friend['location']
        
        if valid and len(itinerary) > max_meetings:
            max_meetings = len(itinerary)
            best_itinerary = itinerary
            if max_meetings == 5:
                print(json.dumps({'itinerary': best_itinerary}))
                exit()

print(json.dumps({'itinerary': best_itinerary}))