import itertools
import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Haight-Ashbury'): 10,
    ('Richmond District', 'Mission District'): 20,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Haight-Ashbury'): 15,
    ('Sunset District', 'Mission District'): 24,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Haight-Ashbury', 'Richmond District'): 10,
    ('Haight-Ashbury', 'Sunset District'): 15,
    ('Haight-Ashbury', 'Mission District'): 11,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Mission District', 'Richmond District'): 20,
    ('Mission District', 'Sunset District'): 24,
    ('Mission District', 'Haight-Ashbury'): 12,
    ('Mission District', 'Golden Gate Park'): 17,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Mission District'): 17,
}

friends = [
    {
        'location': 'Sunset District',
        'name': 'Sarah',
        'start': 645,
        'end': 1140,
        'duration': 30
    },
    {
        'location': 'Haight-Ashbury',
        'name': 'Richard',
        'start': 705,
        'end': 885,
        'duration': 90
    },
    {
        'location': 'Mission District',
        'name': 'Elizabeth',
        'start': 660,
        'end': 1035,
        'duration': 120
    },
    {
        'location': 'Golden Gate Park',
        'name': 'Michelle',
        'start': 1095,
        'end': 1245,
        'duration': 90
    }
]

for perm in itertools.permutations(friends):
    current_time = 540  # 9:00 AM
    current_location = 'Richmond District'
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
    
    if valid and len(itinerary) == 4:
        print(json.dumps({'itinerary': itinerary}))
        exit()

# If no permutation meets all four, check for permutations with fewer friends
max_meetings = 0
best_itinerary = []
for r in range(3, 0, -1):
    for perm in itertools.permutations(friends, r):
        current_time = 540
        current_location = 'Richmond District'
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
            if max_meetings == 3:
                print(json.dumps({'itinerary': best_itinerary}))
                exit()

print(json.dumps({'itinerary': best_itinerary}))