import itertools
import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'The Castro'): 16,
    ('Pacific Heights', 'Sunset District'): 21,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'The Castro'): 17,
    ('Nob Hill', 'Sunset District'): 25,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'The Castro'): 21,
    ('Russian Hill', 'Sunset District'): 23,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('The Castro', 'Pacific Heights'): 16,
    ('The Castro', 'Nob Hill'): 16,
    ('The Castro', 'Russian Hill'): 18,
    ('The Castro', 'Sunset District'): 17,
    ('The Castro', 'Haight-Ashbury'): 6,
    ('Sunset District', 'Pacific Heights'): 21,
    ('Sunset District', 'Nob Hill'): 27,
    ('Sunset District', 'Russian Hill'): 24,
    ('Sunset District', 'The Castro'): 17,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'The Castro'): 6,
    ('Haight-Ashbury', 'Sunset District'): 15,
}

friends = [
    {
        'location': 'Nob Hill',
        'name': 'Ronald',
        'start': 600,  # 10:00 AM
        'end': 1020,   # 5:00 PM
        'duration': 105
    },
    {
        'location': 'Russian Hill',
        'name': 'Sarah',
        'start': 435,  # 7:15 AM
        'end': 570,   # 9:30 AM
        'duration': 45
    },
    {
        'location': 'The Castro',
        'name': 'Helen',
        'start': 810,  # 1:30 PM
        'end': 1020,   # 5:00 PM
        'duration': 120
    },
    {
        'location': 'Sunset District',
        'name': 'Joshua',
        'start': 855,  # 2:15 PM
        'end': 1200,   # 7:30 PM
        'duration': 90
    },
    {
        'location': 'Haight-Ashbury',
        'name': 'Margaret',
        'start': 615,  # 10:15 AM
        'end': 1200,   # 10:00 PM
        'duration': 60
    }
]

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Pacific Heights'
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
    
    if valid and len(itinerary) == 5:
        print(json.dumps({'itinerary': itinerary}))
        exit()

# If no permutation meets all five, check for permutations with fewer friends
max_meetings = 0
best_itinerary = []
for r in range(4, 0, -1):
    for perm in itertools.permutations(friends, r):
        current_time = 540
        current_location = 'Pacific Heights'
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
            if max_meetings == 4:
                print(json.dumps({'itinerary': best_itinerary}))
                exit()

print(json.dumps({'itinerary': best_itinerary}))